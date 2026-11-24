"""Matrix-derived interiors with Schwarzschild initial tides and ordinary matter loading.

All ages and tidal components in the comparison use x/R_* as the inverse time unit.
The exact spin representations are used for the Casimir ratio. No external data,
random sample, curve fit, or observational prediction enters these calculations.
"""
import json
from pathlib import Path

import numpy as np
from scipy import integrate, optimize, special

ROOT = Path(__file__).resolve().parents[1]
GQUAD = dict(epsabs=2.e-12,epsrel=2.e-12,limit=140)
ODE = dict(method='DOP853',rtol=4.e-12,atol=4.e-14)


def ward_check():
    # Evaluate the actual trace action, scalar kinetic term and their derivative
    # with respect to the base symplectic density at fixed embedding.
    h=np.diag([2.,-3.,.8,1.2])
    a,b=.84,.71
    k=.36
    gradients=np.array([[.3,-.8,.4,.6],[-.22,.31,.5,-.1]])
    def fields(s):
        theta=np.zeros((4,4))
        theta[0,1]=s
        theta[1,0]=-s
        theta[2,3]=b
        theta[3,2]=-b
        density=1/(s*b)
        volume=np.sqrt(-np.linalg.det(h))
        inverse=density*theta@h@theta.T/volume
        bare=-volume*np.einsum('ij,ij->',inverse,h)/(4*k)
        kinetic=gradients@inverse@gradients.T
        matter=-volume*np.trace(kinetic)/2
        stress=gradients.T@gradients-np.linalg.inv(inverse)*np.trace(kinetic)/2
        stress_mixed=inverse@stress
        angular=np.trace(stress_mixed[2:,2:])/2
        base=np.trace(stress_mixed[:2,:2])/2
        return bare+matter,volume,inverse,stress,angular-base
    action,volume,inverse,stress,pi=fields(a)
    step=1.e-5
    derivative=(fields(a*np.exp(step))[0]-fields(a*np.exp(-step))[0])/(2*step)
    F=.5*np.trace((inverse@h)[2:,2:])
    expected=volume*((F+1/F)/(2*k)+pi)
    np.testing.assert_allclose(derivative,expected,rtol=2e-10)
    # Vary all independent entries of h to test the full pulled-back tensor,
    # also with off-diagonal base momentum flow and angular stress.
    theta=np.array([[0,a,0,0],[-a,0,0,0],[0,0,0,b],[0,0,-b,0]])
    U=theta.T@stress@theta/(a*b*volume)-np.trace(inverse@stress)*np.linalg.inv(h)/2
    kernel=inverse/k+U
    max_error=0.
    for i in range(4):
        for j in range(i,4):
            dh=np.zeros((4,4))
            dh[i,j]=dh[j,i]=1
            h+=step*dh
            up=fields(a)[0]
            h-=2*step*dh
            down=fields(a)[0]
            h+=step*dh
            max_error=max(max_error,abs((up-down)/(2*step)+volume*np.sum(kernel*dh)/2))
    assert max_error<1e-8
    parts=[]
    for mass,pz,pt in ((0,2.,0),(0,.6,.8),(1,3.,0),(1.7,-2.,.4)):
        energy=np.sqrt(mass**2+pz**2+pt**2)
        D=(energy**2-pz**2+pt**2)/energy
        np.testing.assert_allclose(D,(mass**2+2*pt**2)/energy,atol=1e-14)
        parts.append(dict(mass=mass,parallel_momentum=pz,angular_momentum_norm=pt,D=D))
    return dict(log_symplectic_derivative_error=abs(derivative-expected),
                embedding_variation_error=max_error,gas=parts)


def dust_surface(coefficient,C=2.):
    # Trial Schwarzschild data R_s=1, kappa*rho = coefficient/r^(3/2).
    r=optimize.brentq(lambda x:3*x**4+4*x**7/coefficient**2-C,1.e-10,C**.25)
    def kinetic_coeff(rad):
        d=coefficient*np.sqrt(rad)
        P=2*(C-rad**4)/(np.sqrt(d*d+4*(C-rad**4))+d)
        return -1+coefficient*P/(2*rad**3.5)
    assert kinetic_coeff(.85*r)>0 and kinetic_coeff(min(1.15*r,C**.25))<0
    return dict(dust_coefficient=coefficient,radius=r,dust_principal_time=kinetic_coeff(r),
                low_density_asymptote=(C*coefficient**2/4)**(1/7))


def match(x,S):
    """Analytic data for the two radii and a rotating exterior triplet at R_*."""
    assert x>0 and 0<S<1
    l=(1-x*x)/(2*x)
    m=(1+x*x)/(2*x)
    K=l*l+m*m
    F=np.sqrt((1-S)/K)
    D=x**3*(1+x*x)/(1+x**4)+S*l/K
    z2=(2*D*D-S*(4*x*x-1+F*F*(4*l*l-1)))/(3*S*S)
    if D<=0 or z2<=0:
        raise ValueError('This compact kinetic fraction does not match all tides')
    z=np.sqrt(z2)
    eta=D/(F*np.sqrt(S)*z**3)
    return dict(x=x,S=S,l=l,m=m,F=F,D=D,z=z,eta=eta)


def ranks(x,requested,spin_k=96):
    eta=match(x,requested)['eta']
    internal=1. if spin_k is None else np.sqrt(spin_k*(spin_k+1))
    spin_j=max(1,round((np.sqrt(1+4*(internal/eta)**2)-1)/2))
    actual=internal/np.sqrt(spin_j*(spin_j+1))
    def gap(S):
        return match(x,S)['eta']-actual
    for step in (.00001,.0001,.001,.007,.03,.1):
        lo,hi=requested*(1-step),requested*(1+step)
        if gap(lo)*gap(hi)<=0:
            S=optimize.brentq(gap,lo,hi,xtol=2.e-15)
            break
    else:
        raise RuntimeError("Could not realize both matrix ranks")
    c=match(x,S)
    np.testing.assert_allclose(c['eta'],actual,rtol=2.e-12)
    c.update(spin_j=spin_j,spin_k=(.5 if spin_k is None else spin_k),
             compact_axes=2 if spin_k is None else 3,requested_share=requested)
    return c


def compact_parts(y):
    n=(len(y)-6)//2
    return y[4:4+n],y[4+n:4+2*n]


def compact_force(w,dw):
    if len(w)==1:
        return -2*w**3,-6*w*w*dw
    return -w*(w@w-w*w),-dw*(w@w-3*w*w)-2*w*(w@dw)


def compact_energy(w,dw):
    potential=w[0]**4 if len(w)==1 else sum(w[i]**2*w[j]**2 for i in range(3) for j in range(i))
    return dw@dw+potential


def clock_geometry(y,c):
    """Proper-time scale factors and four independent comoving Riemann components."""
    x,F,eta=c['x'],c['F'],c['eta']
    U,vel=y[:2],y[2:4]
    w,dw=compact_parts(y)
    alpha=np.sqrt(U@U)
    da=U@vel/alpha
    accel=-2*alpha**2*U/x**2
    jerk=-2*(2*(U@vel)*U+alpha**2*vel)/x**2
    ddw,jerkw=compact_force(w,dw)
    M,N=(F*x)**2,(eta*F*x*x)**2
    q=M*(vel@vel)+N*(dw@dw)
    dq=2*(M*(vel@accel)+N*(dw@ddw))
    ddq=2*(M*(accel@accel+vel@jerk)+N*(ddw@ddw+dw@jerkw))
    rad=q**.25
    dr=dq/(4*rad**3)
    ddr=ddq/(4*rad**3)-3*dr*dr/rad
    dda=(vel@vel+U@accel-da**2)/alpha
    beta=alpha/rad
    db=(da-beta*dr)/rad
    ddb=(dda-beta*ddr-2*db*dr)/rad
    lapse=alpha*rad
    dl=da*rad+alpha*dr
    Hr=dr/(lapse*rad)
    Hz=db/(lapse*beta)
    tide=np.array([-(ddb-db*dl/lapse)/(lapse**2*beta),
                   -(ddr-dr*dl/lapse)/(lapse**2*rad),Hz*Hr,1/(x*rad)**2+Hr**2])
    return rad,beta,lapse,dr,Hr,Hz,tide


def initial(c):
    x,F,eta=c['x'],c['F'],c['eta']
    if 'compact_initial' in c:
        return np.r_[1.,0.,c['l']/x,c['m']/x,c['compact_initial'],0.,0.]
    return np.array([1.,0.,c['l']/x,c['m']/x,c['z']/x,np.sqrt(c['S'])/(eta*F*x*x),0.,0.])


def trajectory(c,start,stop,angle_clock=False):
    x,F,eta=c['x'],c['F'],c['eta']
    def rhs(v,y):
        U,vel=y[:2],y[2:4]
        w,dw=compact_parts(y)
        norm=U@U
        q=(F*x)**2*(vel@vel)+(eta*F*x*x)**2*(dw@dw)
        rad=q**.25
        lapse=np.sqrt(norm)*rad
        acc,_=compact_force(w,dw)
        rate=norm*x/c['m'] if angle_clock else 1.
        return rate*np.r_[vel,-2*norm*U/x**2,dw,acc,lapse,lapse/np.sqrt(1+(rad/x)**2/norm)]
    sol=integrate.solve_ivp(rhs,(start,stop),initial(c),dense_output=True,**ODE)
    assert sol.success
    return sol.sol


def gr_radius(age,x):
    # The age is x times the comoving proper time since the joining surface.
    def elapsed(rad):
        return integrate.quad(lambda h:x*np.sqrt(h/(1+x**2-h)),rad,1.,**GQUAD)[0]
    return optimize.brentq(lambda rad:elapsed(rad)-age,.05,1.)


def first_cross(f,start,stop,n=160):
    grid=np.linspace(start,stop,n)
    last=f(grid[0])
    for a,b in zip(grid,grid[1:]):
        val=f(b)
        if last*val<=0:
            return optimize.brentq(f,a,b,xtol=2e-14)
        last=val
    raise RuntimeError("No crossing on the specified interval")


def bounce(c):
    x=c['x']
    y0=initial(c)
    rad,beta,lap,dr,Hr,Hz,tides=clock_geometry(y0,c)
    gr=np.array([-2.,1.,-1.,2.])*(1+x*x)/(2*x*x)
    # This checks R, both extrinsic curvatures and all independent Riemann components.
    match_error=max(abs(rad-1),abs(beta-1),abs(Hr+1),abs(Hz-(1+x*x)/(2*x*x)),
                    float(np.max(abs(tides-gr))/max(abs(gr))))
    assert match_error<2e-10
    sol=trajectory(c,0.,2.4)
    first=first_cross(lambda v:clock_geometry(sol(v),c)[3],0.,2.4)
    y=sol(first)
    minrad=clock_geometry(y,c)[0]
    assert 0<minrad<1
    def tide_depart(v):
        state=sol(v)
        r=gr_radius(state[-2],x)
        actual=clock_geometry(state,c)[-1]
        return np.max(abs(actual/(gr/r**3)-1))-.05
    window=first_cross(tide_depart,0.,min(.12,first),n=65)
    # An independent integral of d tau along the matrix trajectory.
    check=integrate.quad(lambda v:clock_geometry(sol(v),c)[2],0,first,**GQUAD)[0]
    np.testing.assert_allclose(check,y[-2],rtol=4e-10)
    energy0=y0[2:4]@y0[2:4]+1/x**2
    e1=y[2:4]@y[2:4]+(y[:2]@y[:2])**2/x**2
    np.testing.assert_allclose(e1,energy0,rtol=5e-11)
    np.testing.assert_allclose(compact_energy(*compact_parts(y)),compact_energy(*compact_parts(y0)),rtol=3.e-10)
    angle=float(np.arctan2(y[1],y[0]))
    independent=trajectory(c,0.,angle,angle_clock=True)(angle)
    np.testing.assert_allclose(y,independent,rtol=3e-9,atol=3e-10)
    w,_=compact_parts(y0)
    gap=np.sqrt(2)*c['z'] if len(w)==1 else x*np.sqrt(w@w-max(w*w))
    classical=2*x/(3*np.sqrt(1+x*x))
    return dict(data=c,relative_riemann_error_at_join=match_error,turn_v=first,
                first_minimum_radius=minrad,comoving_age_at_turn=y[-2],radial_E1_age_at_turn=y[-1],
                fraction_of_GR_E1_time_to_zero=y[-1]/classical,gram_clock_angle_at_turn=angle,
                five_percent_tidal_age=sol(window)[-2],angular_KK_gap_over_weyl=gap/np.sqrt(1+x*x))


def limit_turn(S):
    alpha=np.sqrt(2*(1-2*S)/3)/S
    slope=S*alpha**3
    amp=(slope**2+alpha**4)**.25
    # cn at its positive first turning point; integrate with a regular endpoint.
    angle=np.arccos(alpha/amp)
    turn=integrate.quad(lambda a:1/(amp*np.sqrt(1+np.cos(a)**2)),0,angle,**GQUAD)[0]
    def readings(v):
        sn,cn,dn,_=special.ellipj(np.sqrt(2)*amp*(v-turn),.5)
        dw=-np.sqrt(2)*amp**2*sn*dn
        rad=(1-S+S*(dw/slope)**2)**.25
        return rad,np.sqrt(1-v+v*v/2)*rad
    age=integrate.quad(lambda v:readings(v)[1],0,turn,**GQUAD)[0]
    np.testing.assert_allclose(readings(0)[0],1.,atol=3e-13)
    return dict(share=S,scaled_compact_amplitude=alpha,turn_v=turn,radius=(1-S)**.25,
                comoving_age=age,proper_fraction_of_GR=1.5*age)


def quantum_compact_turn(share,epsilon,count,steps):
    """Quantize the homogeneous compact coordinate of the deep interior.

    In the scaled clock the Hamiltonian is (p^2+w^4)/2 and [w,p]=i*epsilon.
    Fourier splitting is used only for this reduced quantum problem. The
    classical number used as a reference never enters its time evolution.
    """
    center=np.sqrt(2*(1-2*share)/3)/share
    speed=share*center**3
    spread=np.sqrt(epsilon/(2*np.sqrt(6)*center))
    half_box=8.
    spacing=2*half_box/count
    position=np.arange(count)*spacing-half_box
    momentum=2*np.pi*epsilon*np.fft.fftfreq(count,spacing)
    state=np.exp(-(position-center)**2/(4*spread**2)+1j*speed*position/epsilon)
    state/=np.linalg.norm(state)
    potential=position**4/2
    kinetic=momentum**2/2
    dv=.16/steps
    half_step=np.exp(-.5j*dv*potential/epsilon)
    full_step=np.exp(-1j*dv*kinetic/epsilon)
    initial_energy=(speed**2+epsilon**2/(4*spread**2)
                    +center**4+6*center**2*spread**2+3*spread**4)/2
    radii=[]
    max_energy_drift=0.
    boundary_probability=0.
    momentum_edge_probability=0.
    for i in range(steps+1):
        weights=abs(state)**2
        spectrum=abs(np.fft.fft(state,norm='ortho'))**2
        energy=weights@potential+spectrum@kinetic
        max_energy_drift=max(max_energy_drift,abs(energy/initial_energy-1))
        boundary_probability=max(boundary_probability,np.sum(weights[abs(position)>7.]))
        momentum_edge_probability=max(momentum_edge_probability,np.sum(spectrum[abs(momentum)>.85*max(abs(momentum))]))
        radii.append((1-share+share*(spectrum@(momentum**2))/speed**2)**.25)
        if i<steps:
            state=half_step*np.fft.ifft(full_step*np.fft.fft(half_step*state))
    minimum=int(np.argmin(radii))
    assert 0<minimum<steps
    left,middle,right=radii[minimum-1:minimum+2]
    curvature=left+right-2*middle
    shift=(left-right)/(2*curvature)
    radius=middle-curvature*shift**2/2
    bound=(1-share+share*epsilon**2/(4*speed**2*np.sqrt(2*initial_energy)))**.25
    assert bound<radius and max_energy_drift<2e-6
    assert boundary_probability<1e-16 and momentum_edge_probability<1e-12
    return dict(epsilon=epsilon,S=share,points=count,steps=steps,initial_width=spread,
                initial_energy=initial_energy,initial_radius_moment=radii[0],
                turn_in_v=(minimum+shift)*dv,radius_fourth_moment_root=radius,
                energy_based_lower_bound=bound,energy_relative_drift=max_energy_drift,
                boundary_probability=boundary_probability,momentum_edge_probability=momentum_edge_probability)


def quantum_compact_comparison():
    rows=[]
    for epsilon in (.1,.2,.4):
        coarse=quantum_compact_turn(.2,epsilon,1024,320)
        fine=quantum_compact_turn(.2,epsilon,2048,640)
        for key in ('turn_in_v','radius_fourth_moment_root'):
            np.testing.assert_allclose(coarse[key],fine[key],atol=4e-7,rtol=0)
        rows.append(dict(coarse=coarse,fine=fine))
    return rows


def oscillator(c,ell,nu,age):
    x=c['x']
    geom=trajectory(c,0.,1.8)
    end=optimize.brentq(lambda v:geom(v)[-2]-age,0.,1.8)
    def rhs(v,p):
        U=geom(v)[:2]
        return [p[1],-nu**2*(U@U)*p[0]]
    start=[1/np.sqrt(2*nu)+0j,-1j*np.sqrt(nu/2)]
    sol=integrate.solve_ivp(rhs,(0.,end),start,**ODE)
    assert sol.success
    q,p=sol.y[:,-1]
    omega=nu*np.linalg.norm(geom(end)[:2])
    n=abs((omega*q-1j*p)/np.sqrt(2*omega))**2
    wronskian=-2*np.imag(q.conjugate()*p)
    np.testing.assert_allclose(wronskian,1.,atol=1e-10)
    cov=np.array([[abs(q)**2,(q.conjugate()*p).real],[(q.conjugate()*p).real,abs(p)**2]])
    return dict(ell=ell,v=end,R=clock_geometry(geom(end),c)[0],occupation=n,cov=cov.tolist())


def limiting_oscillator(nu,window,exact_x=None):
    # The two endpoints are equally far from the oscillator minimum v=1.
    if exact_x is None:
        def W(v):
            return nu*np.sqrt(1-v+v**2/2)
    else:
        x=exact_x
        lo=(1-x*x)/(2*x)
        m=(1+x*x)/(2*x)
        init=np.array([1.,0.,lo/x,m/x])
        def rhs0(v,y):
            return np.r_[y[2:],-2*(y[:2]@y[:2])*y[:2]/x**2]
        ends=[integrate.solve_ivp(rhs0,(0.,a),init,dense_output=True,**ODE)
              for a in (1-window,1+window)]
        assert all(s.success for s in ends)
        def W(v):
            return nu*np.linalg.norm(ends[int(v>=0)].sol(v)[:2])
    v0,v1=1-window,1+window
    init=[1/np.sqrt(2*W(v0))+0j,-1j*np.sqrt(W(v0)/2)]
    sol=integrate.solve_ivp(lambda v,y:[y[1],-W(v)**2*y[0]],(v0,v1),init,**ODE)
    assert sol.success
    q,p=sol.y[:,-1]
    np.testing.assert_allclose(-2*np.imag(q.conjugate()*p),1.,atol=1.2e-8)
    end=W(v1)
    return abs((end*q-1j*p)/np.sqrt(2*end))**2


def direct_matrices():
    def spins(j):
        m=np.arange(j,-j-1,-1)
        a=np.diag(np.sqrt((j-m[1:])*(j+m[1:]+1)),1)
        return [(a+a.T)/2,(a-a.T)/2.0j,np.diag(m)]
    J,K=spins(2),spins(1)
    U=np.array([.74,-.32])
    V=np.array([.21,.67])
    b,db=.83,-.36
    X=[np.kron(z,np.eye(3)) for z in J]
    Y=[np.kron(np.eye(5),z) for z in K]
    mats=[u*z for u in U for z in X]+[b*z for z in Y]
    vel=[v*z for v in V for z in X]+[db*z for z in Y]
    acc=[-2*(U@U)*u*z for u in U for z in X]+[-2*b**3*z for z in Y]
    def com(a,b):
        return a@b-b@a
    def double(m,j):
        return sum(com(y,com(y,m[j])) for y in m)
    eom=max(np.linalg.norm(second+double(mats,i)) for i,second in enumerate(acc))
    gauss=np.linalg.norm(sum(com(a,v) for a,v in zip(mats,vel)))
    # Physical ell=1 and ell=2 polarizations along the compact triplet, singlets in its colour.
    leaks=[]
    for ell,T in ((1,X[2]),(2,X[2]@X[2]-2*np.eye(15))):
        eps=1e-5
        up=list(mats);up[6]=up[6]+eps*T
        down=list(mats);down[6]=down[6]-eps*T
        want=ell*(ell+1)*(U@U)*T
        leaks.append(max(np.linalg.norm((double(up,j)-double(down,j))/(2*eps)-(want if j==6 else 0)) for j in range(9)))
    assert max(eom,gauss)<4.e-13 and max(leaks)<4.e-10
    return dict(parent_eom=eom,gauss=gauss,physical_polarization_residual=leaks)


def kinetic_series(position,velocity,order,internal,x):
    """Taylor coefficients of squared speed, directly from the double commutator."""
    coeff=[np.asarray(position),np.asarray(velocity)]
    for n in range(order):
        cubic=np.zeros_like(coeff[0])
        for i in range(n+1):
            for j in range(n-i+1):
                k=n-i-j
                factor=coeff[i]@coeff[j]
                if internal:
                    cubic+=(factor-coeff[i]*coeff[j])*coeff[k]
                else:
                    cubic+=(2/x**2)*factor*coeff[k]
        coeff.append(-cubic/((n+1)*(n+2)))
    speed=[(i+1)*a for i,a in enumerate(coeff[1:])]
    return np.array([sum(speed[i]@speed[n-i] for i in range(n+1)) for n in range(order+1)])


def anisotropic_data(x,S,guess,fixed_spin=None):
    # Use K_i=sigma_i/2. Each square is central even when the three sizes differ.
    l,m=(1-x*x)/(2*x),(1+x*x)/(2*x)
    F=np.sqrt((1-S)/(l*l+m*m))
    ext=(F*x)**2*kinetic_series([1.,0.],[l/x,m/x],4,False,x)
    radius=[1.]
    for n in range(4):
        squared=sum(radius[i]*radius[n-i] for i in range(n+1))
        radius.append((-(1+1/x**2)*radius[n]+squared/x**2)/(n+1))
    sq=np.convolve(radius,radius)
    target=np.convolve(sq,sq)[:5]
    casimir=F*x*x*np.linalg.norm(guess[3:])/(2*np.sqrt(S))
    spin_j=round((np.sqrt(1+4*casimir**2)-1)/2) if fixed_spin is None else fixed_spin
    eta=1/(2*np.sqrt(spin_j*(spin_j+1)))
    factor=(eta*F*x*x)**2
    def residual(free):
        values=np.r_[guess[0],free]
        return (ext+factor*kinetic_series(values[:3],values[3:],4,True,x)-target)/np.maximum(1.,abs(target))
    fit=optimize.least_squares(residual,guess[1:],jac='cs',x_scale='jac',
                               xtol=2e-14,ftol=2e-14,gtol=2e-14,max_nfev=180)
    assert fit.success and max(abs(fit.fun))<2e-10
    c=dict(x=x,S=S,F=F,l=l,m=m,eta=eta,spin_j=spin_j,spin_k=.5,
           compact_initial=[guess[0],*fit.x],fourth_order_residual=max(abs(fit.fun)),
           smallest_scaled_jacobian_singular_value=np.linalg.svd(fit.jac,compute_uv=False)[-1])
    return c


def intrinsic_quantum_comparison(c,d,angle=.48,nu=1.):
    # This test evolves the actual mode in the colour-invariant Gram angle.
    def read(data):
        track=trajectory(data,0.,angle,angle_clock=True)
        def rhs(phi,z):
            U=track(phi)[:2]
            sq=U@U
            return (sq*data['x']/data['m'])*np.array([z[1],-nu*nu*sq*z[0]])
        start=[1/np.sqrt(2*nu)+0j,-1j*np.sqrt(nu/2)]
        sol=integrate.solve_ivp(rhs,(0.,angle),start,**ODE)
        assert sol.success
        end=track(angle)
        np.testing.assert_allclose(np.arctan2(end[1],end[0]),angle,atol=2e-11)
        return sol.y[:,-1],end[-2],clock_geometry(end,data)[0]
    a,at,ar=read(c)
    b,bt,br=read(d)
    np.testing.assert_allclose(a,b,atol=2e-11)
    return dict(gram_angle=angle,proper_readings=[at,bt],radii=[ar,br],
                angular_state_vector_difference=np.linalg.norm(a-b))


def finite_longitudinal_probe(row,h,ell):
    """The ninth spatial matrix is unoccupied in the two-Pauli background."""
    c=row['data']
    assert c['compact_axes']==2 and 0<=ell<=2*c['spin_j']
    x=c['x']
    C=np.sqrt(c['spin_j']*(c['spin_j']+1))
    eps=h*c['F']*x*x/(2*C)
    nu2=ell*(ell+1)/x**2
    end=row['turn_v']
    past=trajectory(c,0.,-1.01*eps)
    future=trajectory(c,0.,end+1.01*eps)
    def geom(v):
        return (past if v<0 else future)(v)
    def kernels(v):
        left,right=geom(v-eps),geom(v+eps)
        dU=right[:2]-left[:2]
        dw=right[4]-left[4]
        longitudinal=(C/x)**2*(dU@dU)+dw*dw
        center=geom(v)
        R=clock_geometry(center,c)[0]
        return (longitudinal+nu2*(right[:2]@left[:2]),
                h*h*R**4+nu2*(center[:2]@center[:2]),(longitudinal/(h*h))**.25)
    direct=[]
    for kind in (0,1):
        start=np.sqrt(kernels(0.)[kind])
        sol=integrate.solve_ivp(lambda v,y:[y[1],-kernels(v)[kind]*y[0]],(0.,end),
                                [1/np.sqrt(2*start)+0j,-1j*np.sqrt(start/2)],**ODE)
        assert sol.success
        q,p=sol.y[:,-1]
        omega=np.sqrt(kernels(end)[kind])
        direct.append(abs((omega*q-1j*p)/np.sqrt(2*omega))**2)
        np.testing.assert_allclose(-2*np.imag(q.conjugate()*p),1.,atol=1e-10)
    series=np.array([kernels(v) for v in np.linspace(0.,end,81)])
    return dict(h=h,ell=ell,half_separation_in_v=eps,
                largest_sampled_frequency_squared_discrepancy=np.max(abs(series[:,0]/series[:,1]-1)),
                radius_read_at_geometric_turn=series[-1,2],radius_read_at_contact=series[0,2],
                occupations_at_geometric_turn=direct)


def scalar_matrix_check():
    # Independent finite-size check of a physical normal mode at nonzero separation.
    j=2
    m=np.arange(j,-j-1,-1)
    L=np.diag(np.sqrt((j-m[1:])*(j+m[1:]+1)),1)
    J=[(L+L.T)/2,(L-L.T)/2.0j,np.diag(m)]
    K=[np.array([[0,1.],[1.,0]])/np.sqrt(2),np.array([[0,-1j],[1j,0]])/np.sqrt(2)]
    U=np.array([.69,-.17]); V=np.array([.43,.26])
    B=.76; D=.58
    def build(u,b):
        return [w*np.kron(z,np.eye(2)) for w in u for z in J]+[b*np.kron(np.eye(5),z) for z in K]
    T=np.kron(J[2]@J[2]-2*np.eye(5),np.eye(2))
    diff=sum(x@(x@T-T@y)-(x@T-T@y)@y for x,y in zip(build(U,B),build(V,D)))
    value=j*(j+1)*((U-V)@(U-V))+(B-D)**2+6*(U@V)
    residual=np.linalg.norm(diff-value*T)
    assert residual<1.e-12
    return residual


def ordinary_colour_preparation():
    """A traceless ordinary matrix correlates the initially separate colours.

    The projection is onto the commutant of the *initial* material colour
    algebra, transported in temporal gauge. Its squared trace norm is
    unchanged by conjugating the material and its reference algebra together.
    """
    U=np.array([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]])
    checks=[]
    for j in (.5,1.,2.,4.):
        m=np.arange(j,-j-1,-1)
        raising=np.diag(np.sqrt((j-m[1:])*(j+m[1:]+1)),1)
        J=[(raising+raising.T)/2,(raising-raising.T)/2j,np.diag(m)]
        C=np.sqrt(j*(j+1))
        n=len(m)
        Y=[np.kron(a,np.eye(2)) for a in J]
        H=sum(np.kron(a,b) for a,b in zip(J,U))/C
        hi,vec=np.linalg.eigh(H)
        gap=(2*j+1)/C
        reduced=lambda y:np.einsum('iaib->ab',y.reshape(n,2,n,2))/n
        peak=8/(3*gap**2)
        err=0.
        for ordinary,sigma in zip(Y,U):
            comm=H@ordinary-ordinary@H
            acceleration=-(H@comm-comm@H)
            err=max(err,np.linalg.norm(reduced(acceleration)-4*sigma/3))
            matrix=vec.conjugate().T@ordinary@vec
            for phase in (.37,1.4,np.pi):
                evolved=vec@(np.cos(phase*(hi[:,None]-hi[None,:])/gap)*matrix)@vec.conjugate().T
                err=max(err,np.linalg.norm(reduced(evolved)-(1-np.cos(phase))*peak*sigma/2))
        assert err<2e-13
        checks.append(dict(spin=j,casimir=C,frequency_gap=gap,peak_internal_axis=peak,
                           peak_squared_norm_fraction=3*peak**2/C**2,direct_matrix_residual=err))
    def rhs(t,y):
        a,b,g,da,db,dg=y
        return [da,db,dg,-8*a**3-2*g*g*(a-b),-8*b**3+2*g*g*(a-b),-8*(a-b)**2*g]
    def energy(y):
        a,b,g,da,db,dg=y
        return 1.5*(da*da+db*db)+.375*dg*dg+6*(a**4+b**4)+3*g*g*(a-b)**2
    # Exact two-Pauli reduction, including evolution of the ordinary source.
    M=sum(np.kron(z,z) for z in U)/2
    sample=np.array([.4,-.35,.7,.13,.8,-.5])
    a,b,g,da,db,dg=sample
    UU=[np.kron(z,np.eye(2)) for z in U]
    VV=[np.kron(np.eye(2),z) for z in U]
    mats=[a*u+b*v for u,v in zip(UU,VV)]+[g*M]
    vel=[da*u+db*v for u,v in zip(UU,VV)]+[dg*M]
    aa,bb,gg=rhs(0,sample)[3:]
    second=[aa*u+bb*v for u,v in zip(UU,VV)]+[gg*M]
    comm=lambda a,b:a@b-b@a
    matrix_error=max(np.linalg.norm(d+sum(comm(y,comm(y,x)) for y in mats)) for x,d in zip(mats,second))
    gauss_error=np.linalg.norm(sum(comm(x,v) for x,v in zip(mats,vel)))
    assert max(matrix_error,gauss_error)<2e-13
    transfer=[]
    for g0 in (.25,1.,2.,4.,8.,32.):
        y0=[1.,0.,g0,0.,0.,0.]
        sol=integrate.solve_ivp(rhs,(0,3./g0),y0,dense_output=True,**ODE)
        assert sol.success
        turn=first_cross(lambda t:sol.sol(t)[0],0,3./g0)
        y=sol.sol(turn)
        e0=energy(y0)
        drift=max(abs(energy(q)/e0-1) for q in sol.y.T)
        assert drift<2.e-9
        target=sol.sol(np.pi/(2*g0))
        transfer.append(dict(seed=g0,first_zero_of_outer=turn,compact_amplitude=y[1],
                             compact_velocity=y[4],positive_compact_energy_share=(1.5*y[4]**2+6*y[1]**4)/e0,
                             amplitude_at_leading_swap_time=target[1],relative_energy_drift=drift))
    return dict(colour_pulses=checks,exact_half_spin=transfer,parent_residual=matrix_error,gauss_residual=gauss_error)


def main():
    samples=[bounce(ranks(x,S)) for x,S in ((2,.20),(8,.20),(64,.20),(512,.12),(512,.20),(512,.38))]
    # The near-horizon existence check uses the matching equations, not the deep-interior approximation.
    edge=[]
    for x in (.08,.25,.5,1.,4.,50.):
        c=match(x,.002*min(1.,x**6))
        *_,curv=clock_geometry(initial(c),c)
        expected=(1+x*x)/(2*x*x)*np.array([-2.,1.,-1.,2.])
        err=float(np.max(abs(curv/expected-1)))
        assert err<1e-8
        edge.append(dict(x=x,R_over_Rs=1/(1+x*x),share=c['S'],casimir_ratio=c['eta'],tide_relative_error=err))
    clocks=[]
    for ell in (128,512,1024):
        nu=np.sqrt(ell*(ell+1))/512
        for age in (.26,.59):
            pairs=[oscillator(samples[n]['data'],ell,nu,age) for n in (3,5)]
            F=1/np.sqrt(np.linalg.det(np.array(pairs[0]['cov'])+np.array(pairs[1]['cov'])))
            assert F<=1+1e-10
            clocks.append(dict(age=age,nu=nu,states=pairs,squared_vacuum_overlap=F,
                               equal_prior_success=(1+np.sqrt(max(0.,1-F)))/2))
    weber=[]
    for nu in (.5,1.,2.):
        exact=np.exp(-np.pi*nu/np.sqrt(2))
        rows=[dict(window=w,limiting_kernel=limiting_oscillator(nu,w)) for w in (6,12,28)]
        # Larger window convergence is oscillatory; compare with the asymptotic formula and with finite x.
        assert abs(rows[-1]['limiting_kernel']-exact)<.003
        rows[0]['finite_x_4096']=limiting_oscillator(nu,6,4096.)
        assert abs(rows[0]['finite_x_4096']-rows[0]['limiting_kernel'])<.0001
        weber.append(dict(nu=nu,infinite_window=exact,profiles=rows))
    anis=[bounce(anisotropic_data(512.,S,q)) for S,q in
          ((.8,[5.9691791,9.0230583,2.1797419,19.9568834,46.9074762,-53.6049767]),
           (.95,[5.1472406,7.7541806,1.8285353,13.8318997,34.1560745,-39.5659725]))]
    # Change only internal initial shape at the same two representation ranks.
    # Keep the kinetic share and the first five radial Taylor coefficients fixed.
    reference=anis[0]['data']
    seed=reference['compact_initial'].copy()
    for step in (1,2,3):
        seed[0]=reference['compact_initial'][0]-.25*step
        second=anisotropic_data(512.,reference['S'],seed,reference['spin_j'])
        seed=second['compact_initial'].copy()
    alternate=bounce(second)
    assert abs(anis[0]['first_minimum_radius']-alternate['first_minimum_radius'])>.003
    comparison=intrinsic_quantum_comparison(reference,second)
    ell=1024
    nu=np.sqrt(ell*(ell+1))/512
    states=[oscillator(c,ell,nu,.26) for c in (reference,second)]
    overlap=1/np.sqrt(np.linalg.det(np.array(states[0]['cov'])+np.array(states[1]['cov'])))
    assert 0<overlap<1
    fixed_rank=dict(first=anis[0],second=alternate,same_angle=comparison,proper_age=.26,
                    states=states,equal_prior_success=(1+np.sqrt(1-overlap))/2)
    two_axis=[]
    for share in (.12,.2,.38):
        row=bounce(ranks(512.,share,spin_k=None))
        row['normal_matrix_wave']=[finite_longitudinal_probe(row,h,128) for h in (.25,.75,1.5)]
        two_axis.append(row)
    return dict(matter_ward=ward_check(),dust=[dust_surface(n) for n in (.10,.015,.001)],
                full_matrix_check=direct_matrices(),finite_spins=samples,arbitrary_radius_examples=edge,
                limiting_bounces=[limit_turn(S) for S in (.12,.20,.38)],same_proper_clock=clocks,
                same_matrix_angle=intrinsic_quantum_comparison(samples[3]['data'],samples[5]['data']),
                anisotropic_compact=anis,fixed_rank_interiors=fixed_rank,two_axis_physical_probe=two_axis,
                finite_separation_matrix_residual=scalar_matrix_check(),quantum_limit=weber,
                quantized_compact_mode=quantum_compact_comparison(),
                ordinary_colour_preparation=ordinary_colour_preparation())


if __name__=='__main__':
    out=ROOT/'verification'/'cat-compact-interior-results.json'
    out.write_bytes((json.dumps(main(),indent=2,allow_nan=False)+'\n').encode('utf8'))

