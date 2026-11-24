"""Matrix projection and self-bound, flavour-charged configurations in the XYZ sector."""
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import cumulative_trapezoid, quad, simpson, solve_bvp
from scipy.linalg import eig_banded, eigh_tridiagonal, null_space
from scipy.optimize import brentq
from scipy.special import expit, spherical_jn


def projection():
    identity = np.eye(2, dtype=complex)
    pauli = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]])
    basis = np.array([identity, *pauli])
    group = [identity, *[1j*t for t in pauli]]
    signs = np.array([[1,1,1], [1,-1,-1], [-1,1,-1], [-1,-1,1]])
    def coordinates(matrix):
        return np.array([np.trace(b @ matrix)/2 for b in basis])
    ranks = []
    for character in [np.ones(4), *signs.T]:
        columns = [coordinates(sum(c*g@b@g.conj().T for g,c in zip(group,character))/4) for b in basis]
        projector = np.stack(columns, axis=1)
        np.testing.assert_allclose(projector@projector, projector, atol=1e-14)
        ranks.append(int(np.linalg.matrix_rank(projector)))
    assert ranks == [1,1,1,1]
    fields = np.array([.3+.7j,-.9+.4j,.2-1.2j])
    matrices = [t*z/2 for t,z in zip(pauli,fields)]
    commutator = lambda a,b: a@b-b@a
    cubic = np.trace(matrices[0]@commutator(matrices[1],matrices[2]))
    np.testing.assert_allclose(cubic, .5j*np.prod(fields))
    for m in matrices:
        np.testing.assert_allclose(commutator(m,m.conj().T), 0, atol=1e-14)
    potential = sum(np.linalg.norm(commutator(matrices[i],matrices[j]))**2
                    for i,j in ((0,1),(1,2),(0,2)))
    np.testing.assert_allclose(potential, .5*sum(abs(fields[i]*fields[j])**2
                                                for i,j in ((0,1),(1,2),(0,2))))
    return ranks


def profile(nu, gravity=0., seed=None):
    """x=|g| v s, gamma=v^2/M_P^2, u/x=2 G M(s)/s, lapse=exp(delta)*sqrt(N)."""
    wall_radius = 2/nu**2
    end = wall_radius+27/math.sqrt(1-nu**2)
    grid = np.linspace(0,end, int(14*end)+1)
    tail = math.sqrt(1-nu**2)
    if seed is None:
        angle = np.arctan(np.exp(wall_radius-grid))
        initial = np.vstack([angle,-np.sin(angle)*np.cos(angle),0*grid,0*grid])
    else:
        initial = seed.sol(grid)
    def equation(x,y):
        angle, flux, mass, delta = y
        metric = 1-np.divide(mass,x,out=np.zeros_like(x),where=x!=0)
        lapse = np.exp(delta)
        s, c = np.sin(angle), np.cos(angle)
        gradient = flux/(metric*lapse)
        rotation = nu**2*s*s/(metric*lapse**2)
        density = metric*gradient**2+(s*c)**2+rotation
        return np.vstack([gradient, lapse*s*c*(np.cos(2*angle)-nu**2/(lapse**2*metric)),
                          gravity*x*x*density, gravity*x*(gradient**2+rotation/metric)])
    def boundary(left,right):
        n = 1-right[2]/end
        return np.array([left[1],left[2],right[3],right[1]/(np.exp(right[3])*n)+(tail+1/end)*right[0]])
    singular = np.diag([0.,-2.,0.,0.])
    solution = solve_bvp(equation,boundary,grid,initial,S=singular,tol=1.5e-8,max_nodes=18000)
    assert solution.success, solution.message
    points = np.linspace(0,end,4501)
    angle, flux, mass, delta = solution.sol(points)
    n = 1-np.divide(mass,points,out=np.zeros_like(points),where=points!=0)
    a = np.exp(delta)
    sine, cosine = np.sin(angle), np.cos(angle)
    grad = flux/(n*a)
    rotation = nu**2*sine**2/(a*a*n)
    density = n*grad**2+(sine*cosine)**2+rotation
    integ = lambda values: simpson(values, x=points)
    q = 8*np.pi*nu*integ(points**2*sine**2/(a*n))
    energy = 4*np.pi*integ(points**2*density)
    assert angle[0] > .7 and min(n)>.8 and np.max(np.diff(angle))<1e-8
    if gravity>0:
        np.testing.assert_allclose(4*np.pi*mass[-1]/gravity,energy,rtol=2e-7)
    wall = brentq(lambda p: solution.sol(p)[0]-math.pi/4,0,end)
    row = dict(nu=nu, gravity=gravity, central_angle=angle[0], half_amplitude_radius=wall,
               q=q,e=energy,energy_over_free_mass=energy/q,maximum_compactness=float(max(1-n)),
               central_lapse=a[0], boundary= end)
    if gravity==0:
        virial = integ(points**2*(grad**2+3*(sine*cosine)**2-3*rotation))
        assert abs(4*np.pi*virial/energy)<1e-7
        sample = wall+8/tail
        samples = np.array([sample,sample+2/tail])
        amplitudes = np.sin(solution.sol(samples)[0])*samples*np.exp(tail*samples)
        np.testing.assert_allclose(amplitudes[0],amplitudes[1],rtol=2e-6)
        row["yukawa_amplitude"] = float(amplitudes[-1])
    return solution,row


def hessian(solution, nu, end, spacing):
    """Fixed-charge radial Hessian including its nonlocal rank-one term."""
    intervals = math.ceil(end/spacing)
    step = end/intervals
    x = step*np.arange(1,intervals)
    theta = solution.sol(x)[0]
    potential = np.cos(4*theta)-nu**2*np.cos(2*theta)
    diagonal, offdiag = 2/step**2+potential, np.full(len(x)-1,-1/step**2)
    eig, vectors = eigh_tridiagonal(diagonal,offdiag,lapack_driver="stev")
    direction = x*np.sin(2*theta)
    inertia = np.sum((x*np.sin(theta))**2)
    weights = (vectors.T@direction)**2*nu**2/inertia
    def secular(z):
        return 1+np.sum(weights/(eig-z))
    fixed = brentq(secular,eig[0]+1e-10,eig[1]-1e-10)
    angular = [eigh_tridiagonal(diagonal+l*(l+1)/x**2,offdiag,select="i",
                                select_range=(0,0),eigvals_only=True)[0] for l in (1,2)]
    assert eig[0]<0<eig[1] and fixed>0 and angular[1]>0
    return dict(step=step, fixed_frequency_min=eig[0],fixed_charge_min=fixed,
                translation=angular[0],quadrupole_static=angular[1])


def mode_clock():
    def frequency(l):
        def characteristic(z):
            return ((l*(l+1)-2-z*z)*spherical_jn(l,z,derivative=True)-4*z*spherical_jn(l,z))
        intervals=np.linspace(.01,8,200)
        for a,b in zip(intervals,intervals[1:]):
            if characteristic(a)*characteristic(b)<0:
                return brentq(characteristic,a,b)
        raise RuntimeError("No radial mode in the search interval")
    roots = [frequency(l) for l in (0,2,3)]
    wave = roots[1]
    reduced = -quad(lambda u:(1-u*u)*(3+u*u)*np.cos(wave*u),-1,1)[0]
    direct = quad(lambda u:((6*(1-u*u)**2-8*(1-u*u))*np.cos(wave*u)
                            -wave*u*(1-u*u)**2*np.sin(wave*u)),-1,1)[0]
    np.testing.assert_allclose(reduced,direct)
    assert 0<wave<np.pi/2 and reduced<0
    return dict(breathing=roots[0],quadrupole=wave,octupole=roots[2],tt_overlap_over_pi_tension_R=reduced)


def finite_wall_clock(sol, nu, radius, end, spacing):
    """Zero of the coupled radial and phase wave operator; Fourier transform of its stress."""
    intervals = math.ceil(end/spacing)
    step = end/intervals
    x = step*np.arange(1,intervals)
    theta, grad = sol.sol(x)[:2]
    cosine = np.cos(theta)
    base = 2/step**2+6/x**2
    radial = base+np.cos(4*theta)-nu**2*np.cos(2*theta)
    phase = base+cosine**2*(np.cos(2*theta)-nu**2)-grad**2
    def mode(energy, vector=False):
        band = np.zeros((3,2*len(x)))
        band[0,::2], band[0,1::2] = radial-energy**2, phase-energy**2
        band[1,::2] = -2*nu*energy*cosine
        band[2,:-2] = -1/step**2
        return eig_banded(band,lower=True,eigvals_only=not vector,select="i",select_range=(0,0))
    frequency = brentq(lambda e:mode(e)[0],0,min(.98*(1-nu),2/radius))
    _,vectors=mode(frequency,True)
    displacement=vectors[::2,0]/x
    displacement *= -sol.sol(radius)[1]/np.interp(radius,x,displacement)
    derivative=np.gradient(displacement,step,edge_order=2)
    u, weights=np.polynomial.legendre.leggauss(36)
    wave = np.cos(np.outer(x*frequency,u))
    w1=wave@(weights*(1-u*u)**2)
    w2=wave@(weights*(4*(1-u*u)-2*(1-u*u)**2))
    overlap=4*simpson(x*x*grad*(derivative*w1+displacement*w2/x),x=x)/radius
    assert frequency<1-nu and overlap<0
    return dict(step=step,frequency_over_m=frequency,frequency_times_radius=radius*frequency,
                tt_overlap_over_pi_tension_R=overlap)


def exchange(sol, row):
    nu, radius, end = row["nu"],row["half_amplitude_radius"],row["boundary"]
    delta = .0004
    sides = []
    for frequency in (nu-delta,nu+delta):
        neighbor,record = profile(frequency,seed=sol)
        clock=finite_wall_clock(neighbor,frequency,record["half_amplitude_radius"],record["boundary"],.08)
        sides.append((record,clock["frequency_over_m"]))
    qprime=(sides[1][0]["q"]-sides[0][0]["q"])/(2*delta)
    eprime=(sides[1][0]["e"]-sides[0][0]["e"])/(2*delta)
    np.testing.assert_allclose(eprime/qprime,nu,rtol=2e-5)
    clock=row["finite_wall_clock"][-1]["frequency_over_m"]
    sensitivity=nu*(sides[1][1]-sides[0][1])/(2*delta*clock)
    assert qprime<0 and 1.5<sensitivity<2.5
    k=math.sqrt(1-nu**2)
    amp=row["yukawa_amplitude"]
    cases=[]
    for gap in (20.,30.,40.):
        distance=2*radius+gap
        mid=distance/2
        # Full stationary profiles on the median plane. At large distance
        # switch to the measured homogeneous tail, outside the radial box.
        def tail(r):
            if r<end:
                theta,theta_prime=sol.sol(r)[:2]
                return np.sin(theta),np.cos(theta)*theta_prime
            f=amp*math.exp(-k*r)/r
            return f,-(k+1/r)*f
        def slice_flux(r):
            f,df=tail(r)
            return -4*math.pi*distance*f*df
        current=quad(slice_flux,mid,end+14,epsabs=1e-28)[0]
        yukawa=8*math.pi*amp**2*math.exp(-k*distance)/distance
        np.testing.assert_allclose(current,yukawa,rtol=2e-6,atol=1e-28)
        rate=math.sqrt(-2*current/qprime)
        cycles=1000
        argument=2*math.pi*cycles*rate/clock
        # Initial equal charges/phases; small, constant differential lapse.
        shift=sensitivity*2*math.sinh(argument/2)**2
        cases.append(dict(surface_gap_times_m=gap,centre_distance_times_m=distance,
                          coupling_times_g2_over_m=current,growth_rate_over_m=rate,
                          growth_exponent_in_1000_cycles=argument,exchange_redshift_deviation=shift))
    return dict(dq_dnu=qprime,clock_sensitivity=sensitivity,measurements=cases)


def gravitational_variations(sol,row):
    """Constraint-reduced ADM energy at fixed charge, with independent momentum variations."""
    end,nu,gamma=row["boundary"],row["nu"],row["gravity"]
    x=np.linspace(0,end,2601)
    angle,flux,mass,delta=sol.sol(x)
    n=1-np.divide(mass,x,out=np.zeros_like(x),where=x!=0)
    a=np.exp(delta)
    f,c=np.sin(angle),np.cos(angle)
    gradient=flux/(a*n)
    conjugate=nu*f/(a*n)
    b=gradient**2+conjugate**2
    potential=(f*c)**2
    def outer(values):
        return -cumulative_trapezoid(values[::-1],x[::-1],axis=0,initial=0)[::-1]
    np.testing.assert_allclose(-gamma*outer(x*b),delta,atol=3e-8)
    def energy_charge(angles,deriv,mom):
        kinetic=deriv**2+mom**2
        e=4*np.pi*simpson(x*x*(kinetic+(np.sin(angles)*np.cos(angles))**2)*
                           np.exp(-gamma*outer(x*kinetic)),x=x)
        q=8*np.pi*simpson(x*x*mom*np.sin(angles),x=x)
        return e,q
    e,q=energy_charge(angle,gradient,conjugate)
    np.testing.assert_allclose([e,q],[row["e"],row["q"]],rtol=1e-7)
    # Differentiating the stationary energy and sourcing the linear scalar
    # equation with the material trace measure the same extended-body charge.
    weight=x*x*a*(b+potential)
    sensitivity=1+2*simpson(weight*delta,x=x)/simpson(weight,x=x)
    rotation=nu**2*f**2/(a*a*n)
    trace=4*np.pi*simpson(x*x*a*(2*n*gradient**2-2*rotation+4*potential),x=x)/row["e"]
    np.testing.assert_allclose(sensitivity,trace,rtol=8e-8)
    row["scalar_sensitivity"] = dict(fixed_charge_ADM=sensitivity,integrated_trace=trace)
    def hessian(order):
        # Smooth radial variations with regular origin and zero outer value.
        k=(np.arange(order)+1)*np.pi/end
        modes=spherical_jn(0,np.outer(x,k))
        derivs=spherical_jn(0,np.outer(x,k),derivative=True)*k[None,:]
        scale=np.sqrt(simpson(x[:,None]**2*modes**2,x=x,axis=0))
        modes,derivs=modes/scale,derivs/scale
        zeros=np.zeros_like(modes)
        s=np.column_stack((modes,zeros))
        ds=np.column_stack((derivs,zeros))
        p=np.column_stack((zeros,modes))
        charge_grad=simpson(x[:,None]**2*(f[:,None]*p+(conjugate*c)[:,None]*s),x=x,axis=0)
        tangent=null_space(charge_grad[None,:])
        dB=2*(gradient[:,None]*ds+conjugate[:,None]*p)
        dU=(np.sin(4*angle)/2)[:,None]*s
        dK=gamma*outer(x[:,None]*dB)
        # Simpson weights on this uniform, even-interval grid.
        w=np.ones(len(x)); w[1:-1:2]=4; w[2:-1:2]=2
        w=w*(x[1]-x[0])/3*x*x
        def pair(l,weight,r):
            return l.T@((w*weight)[:,None]*r)
        metric=(pair(ds,a*n,ds)+pair(p,a*n,p)+pair(s,a*np.cos(4*angle)+nu*conjugate*f,s)
                +.5*pair(dK,a*(b+potential),dK))
        cross=pair(dB+dU,a,dK)+2*nu*pair(s,c,p)
        metric-=(cross+cross.T)/2
        test=tangent[:,0]
        s0,ds0,p0=s@test,ds@test,p@test
        def fixed_path(eps):
            theta=angle+eps*s0
            pi=conjugate+eps*p0
            _,trial_q=energy_charge(theta,gradient+eps*ds0,pi)
            return energy_charge(theta,gradient+eps*ds0,pi*q/trial_q)[0]
        step=.003
        curvature=(fixed_path(step)+fixed_path(-step)-2*e)/(8*np.pi*step**2)
        np.testing.assert_allclose(curvature,test@metric@test,rtol=7e-5,atol=1e-6)
        return dict(radial_basis_order=order,constrained_min=float(np.linalg.eigvalsh(tangent.T@metric@tangent)[0]))
    rows=[hessian(o) for o in (12,24,48)]
    assert 0 < rows[-1]["constrained_min"] <= rows[0]["constrained_min"]
    return rows


def dilute_branch():
    """An independent Newtonian seed followed by the full regular Einstein equations."""
    z=np.linspace(0,26,551)
    f=1.1/np.cosh(z)
    phi=-1.7/np.sqrt(1+z*z)
    def newton(x,y):
        f,df,u,du=y
        return np.vstack([df,(1+2*u)*f,du,f*f])
    def edges(left,right):
        return [left[1],left[3],right[0]+right[1],right[2]+z[-1]*right[3]]
    initial=np.vstack([f,-f*np.tanh(z),phi,1.7*z/(1+z*z)**1.5])
    sn=solve_bvp(newton,edges,z,initial,S=np.diag([0,-2,0,-2]),tol=2e-9,max_nodes=9000)
    assert sn.success and sn.sol(0)[0]>.3
    f,df,u,du=sn.sol(z)
    mass0=2*z*z*du
    initial=np.vstack([f,df,mass0,u+z*du])
    examples=[]
    for eps in (.075,.045):
        gravity=.5  # zeta=1, no large Einstein coefficient.
        eps2=eps**2
        nu=math.sqrt(1-eps2)
        angle_scale=eps2/math.sqrt(gravity)
        def eq(x,y):
            f,flux,mass,delta=y
            ratio=np.divide(mass,x,out=np.zeros_like(x),where=x!=0)
            metric=1-eps2*ratio
            a=np.exp(eps2*delta)
            theta=angle_scale*f
            sine,cosine=np.sin(theta),np.cos(theta)
            gradient=flux/(a*metric)
            kinetic=(nu*sine/angle_scale/a)**2/metric
            local_scaled=(1-ratio+metric*np.expm1(2*eps2*delta)/eps2)/(a*a*metric)
            force=a*(sine/angle_scale)*cosine*(local_scaled-2*(sine/eps)**2)
            density=metric*eps2*gradient**2+((sine/angle_scale)*cosine)**2+kinetic
            return np.vstack([gradient,force,x*x*density,x*(eps2*gradient**2+kinetic/metric)])
        def bc(left,right):
            n=1-eps2*right[2]/z[-1]
            return [left[1],left[2],right[3],right[1]/n+right[0]]
        sol=solve_bvp(eq,bc,z,initial,S=np.diag([0,-2,0,0]),tol=5e-9,max_nodes=8000)
        assert sol.success,sol.message
        x=np.linspace(0,z[-1],3201)
        f,flux,mass,delta=sol.sol(x)
        theta=angle_scale*f
        n=1-eps2*np.divide(mass,x,out=np.zeros_like(x),where=x!=0)
        a=np.exp(eps2*delta)
        local=x*x*(np.sin(theta)/angle_scale)**2/(a*n)
        cumulative=cumulative_trapezoid(local,x,initial=0)
        rhalf=np.interp(cumulative[-1]/2,cumulative,x)/eps
        q=8*np.pi*nu*eps/gravity*simpson(local,x=x)
        energy=4*np.pi*eps/gravity*mass[-1]
        assert min(f)>-1e-10 and .99<energy/q<1 and max(1-n)<.03
        examples.append(dict(epsilon=eps,nu=nu,zeta=1.,q=q,e=energy,energy_over_free_mass=energy/q,
                             central_angle=theta[0],half_charge_radius=rhalf,
                             maximum_compactness=float(max(1-n)),central_lapse=a[0]))
    return examples


def minimal_scalar(trial_frequency):
    """Control with a constant Einstein coefficient and negligible self-gravity."""
    nu=trial_frequency
    target_charge=4*math.pi**2/nu**2
    radius=math.pi/nu
    tail=math.sqrt(1-nu**2)
    end=radius+38/tail
    x=np.linspace(0,end,701)
    inside=x<radius
    f=np.where(inside,spherical_jn(0,nu*x),0.)
    df=np.where(inside,nu*spherical_jn(0,nu*x,derivative=True),0.)
    h=np.maximum(0.,1-radius/np.maximum(x,radius))
    dh=np.where(inside,0.,radius/np.maximum(x,radius)**2)
    def eq(x,y,param):
        f,df,h,dh,_=y
        frequency=expit(param[0])
        return np.vstack((df,(h*h-frequency**2)*f,dh,f*f*h,8*np.pi*frequency*x*x*f*f))
    def bc(left,right,param):
        frequency=expit(param[0])
        asymptote=math.sqrt(max(1-frequency**2,1e-14))
        c=end**2*right[3]
        return [left[1],left[3],left[4],right[1]+(asymptote+(1-c/asymptote)/end)*right[0],
                right[2]+end*right[3]-1,right[4]-target_charge]
    charge_guess=cumulative_trapezoid(x*x*f*f,x,initial=0)
    charge_guess*=target_charge/charge_guess[-1]
    sol=solve_bvp(eq,bc,x,np.vstack((f,df,h,dh,charge_guess)),p=[math.log(nu/(1-nu))],
                  S=np.diag([0,-2,0,-2,0]),tol=1e-8,max_nodes=14000)
    assert sol.success, sol.message
    nu=expit(sol.p[0])
    x=np.linspace(0,end,4001)
    f,df,h,dh,_=sol.sol(x)
    charge=8*math.pi*nu*simpson(x*x*f*f,x=x)
    c=end**2*dh[-1]
    energy=4*math.pi*(simpson(x*x*(df**2+dh**2+(h*h+nu**2)*f*f),x=x)+c*c/end)
    np.testing.assert_allclose(energy,8*math.pi*c,rtol=2e-7)
    assert f[0]>.1 and energy<charge
    return dict(nu=nu,q=charge,e=energy,scalar_tail=c,energy_over_free_mass=energy/charge)


def density_comparison(row):
    # R is the angular wall midpoint; this comparison uses the total ADM mass.
    prefactor=row["e"]/(8*math.pi*row["half_amplitude_radius"])
    newton,light_speed=6.67430e-11,299792458.
    cases=[]
    for mass,radius in [(70.,.3),(1.31e-9,5e-5)]:
        compactness=2*newton*mass/(light_speed**2*radius)
        cases.append(dict(mass_kg=mass,radius_m=radius,compactness=compactness,
                          zeta_for_one_dense_droplet=prefactor/compactness))
    return cases


def bounds_on_scale_coupling():
    # The lower edge of the two-sided 95% interval of the Cassini measurement.
    negative_extent=(1.96*2.3-2.1)*1e-5
    beta_limit=negative_extent/(2-negative_extent)
    examples=[]
    for zeta in (1.,1e4):
        # d=F0/(2*zeta*v**2). The connected positive-F region has d>-1.
        slope=beta_limit/zeta
        radical=math.sqrt(slope**2+8*beta_limit*(6+1/zeta))
        lower,upper=(slope-radical)/4,(slope+radical)/4
        for d in (lower,upper):
            np.testing.assert_allclose(2*d*d/(6+(1+d)/zeta),beta_limit)
        examples.append(dict(zeta=zeta,bare_to_induced_interval=[lower,upper],
                             absolute_mass_slope_mismatch_at_zero_bare=
                             math.sqrt(beta_limit*(6+1/zeta)/2)))
    return dict(two_sided_95_negative_extent=negative_extent,universal_force_ratio_limit=beta_limit,
                minimum_v_over_reduced_Planck_minimal=1/math.sqrt(beta_limit),families=examples)


def compact_sphere():
    """Ordered IKKT mixed term on a product brane, at fourth order in the fluxes."""
    def divided_log(a,b):
        return math.log1p((b-a)/a)/(b-a) if a!=b else 1/a
    # In 4d the two external torsion insertions supply k**2. The three
    # distinct propagator orderings give the divided difference of the log.
    for a,b in ((2.,2.),(.7,3.),(1.7,.32)):
        def ordered(k):
            s,t=1/(k*k+a),1/(k*k+b)
            return 2*k**5*(s**3*t+s*s*t*t+s*t**3)
        np.testing.assert_allclose(quad(ordered,0,np.inf)[0],divided_log(a,b),rtol=1e-12)
    def angular_momentum(ell):
        mag=np.arange(-ell,ell+1)
        ladder=np.diag(np.sqrt((ell-mag[:-1])*(ell+mag[:-1]+1)),-1)
        return [(ladder+ladder.T)/2,(ladder-ladder.T)/(2j),np.diag(mag)]
    def shape_sum(angular,eps):
        scales=np.exp([eps,-eps,0.])
        total=0.
        for spin in angular:
            masses,rotation=np.linalg.eigh(sum(s*s*j@j for s,j in zip(scales,spin)))
            weights=np.array([[divided_log(a,b) for b in masses] for a in masses])
            for s,j in zip(scales,spin):
                flux=(rotation.conj().T@j@rotation)/s
                total+=np.sum(weights*abs(flux)**2)
        return total
    cases=[]
    for size in (2,3,5,9,16):
        angular=[angular_momentum(ell) for ell in range(1,size)]
        count=size**2-1
        def analytic(ell):
            cas=ell*(ell+1)
            return (8-4/cas)*(4*cas-3)/(30*cas)
        k=sum((2*ell+1)*analytic(ell) for ell in range(1,size))/count
        base=shape_sum(angular,0.)
        np.testing.assert_allclose(base,count,rtol=2e-14)
        step=.0008
        samples=[shape_sum(angular,eps)/base for eps in (step,step/2)]
        # sum_i(eps_i**2)=2 eps**2. The shape is even in this deformation.
        fitted=[(sample-1)/(2*eps**2) for sample,eps in zip(samples,(step,step/2))]
        extrapolated=(4*fitted[1]-fitted[0])/3
        np.testing.assert_allclose(extrapolated,k,rtol=2e-7)
        assert 2/3-2*k<0
        cases.append(dict(matrix_rank=size,shape_coefficient_log_kernel=k,
                          shape_coefficient_from_matrices=extrapolated,
                          stationary_shear_curvature_coefficient=2/3-2*k,
                          cK_squared=np.pi**2*count/4,lightest_G_times_mass_squared=4*np.pi/count))
    return cases


def main():
    solutions, rows = {},[]
    for nu in (.67,.55,.45,.36,.30):
        sol,r = profile(nu)
        solutions[nu]=sol
        rows.append(r)
    for nu in (.55,.36):
        row = next(r for r in rows if r["nu"]==nu)
        row["hessians"]=[hessian(solutions[nu],nu,row["boundary"],dx) for dx in (.12,.08)]
        a,b=row["hessians"]
        assert abs(b["translation"])<.55*abs(a["translation"])
        row["finite_wall_clock"]=[finite_wall_clock(solutions[nu],nu,row["half_amplitude_radius"],
                                                     row["boundary"],dx) for dx in (.12,.08)]
    example=next(r for r in rows if r["nu"]==.36)
    leakage=exchange(solutions[.36],example)
    sol, grav=profile(.36,gravity=.00005,seed=solutions[.36])
    grav["adm_hessians"]=gravitational_variations(sol,grav)
    result=dict(projector_ranks=projection(), self_bound_profiles=rows,
                einstein_profile=grav, geometric_clock=mode_clock(), exchange=leakage,
                dilute_einstein=dilute_branch(), minimal_scalar=[minimal_scalar(nu) for nu in (.40,.48)],
                scale_force=bounds_on_scale_coupling(),
                round_compact_one_loop=compact_sphere(),
                macroscopic_comparison=density_comparison(example))
    target = Path(__file__).resolve().parents[1]/"verification"/"cat-charge-droplet-results.json"
    target.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")


if __name__=="__main__":
    main()
