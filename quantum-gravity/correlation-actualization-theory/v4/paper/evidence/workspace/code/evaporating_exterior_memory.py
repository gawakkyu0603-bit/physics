"""Maxwell transport through a finite Vaidya endpoint and its spin flux.

G=c=hbar=1. Mass and retarded time have dimensions of length. The frequency
w is conjugate to dimensionless similarity time. No random numbers are used.
"""
import argparse
import json
import math
from functools import lru_cache
from itertools import product
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import eval_legendre, roots_legendre

ROOT = Path(__file__).resolve().parents[1]


def horizon_radii(nu):
    discr = math.sqrt(1-16*nu)
    return 4/(1+discr), (1+discr)/(4*nu)


@lru_cache(maxsize=None)
def transfer(nu, ell, w, resolution=1):
    # Regular outgoing retarded solution on the two sides of the outer
    # similarity horizon. Use its Frobenius coefficients there, not a
    # prescribed absorbing condition at the end of the physical spacetime.
    lo, hi = horizon_radii(nu)
    zb = 1.15*lo
    ang = ell*(ell+1)
    def f(z):
        return -2*nu*(z-hi)*(z-lo)/z
    def fp(z):
        return 2/z**2-2*nu
    slope = ang/hi**2/(fp(hi)+2j*w)
    quadratic = (ang*(slope/hi**2-2/hi**3)+4*slope/hi**3)/(4*(fp(hi)+1j*w))
    def solve(end, side):
        start = math.log1p(side*(2e-6 if resolution else 1e-5))
        z = hi*math.exp(start)
        dz = z-hi
        state = [1+slope*dz+quadratic*dz**2,z*(slope+2*quadratic*dz)]
        def equation(v, pair):
            pos = hi*math.exp(v)
            return [pair[1],(ang*pair[0]-(pos*fp(pos)-f(pos)+2j*w*pos)*pair[1])/f(pos)]
        sol=solve_ivp(equation,[start,end],state,method="DOP853",
                      rtol=2e-11 if resolution else 3e-9,atol=2e-13 if resolution else 3e-11)
        assert sol.success
        return sol.y[:,-1]
    edge, edge_x=solve(math.log(zb/hi),-1)
    lambda_w=w/nu
    end=21. if resolution else 17.
    y, dx=solve(end,1)
    # Leading 1/z correction to both asymptotic powers. Without this
    # the tiny reflection at high frequency is contaminated by the tail.
    z=hi*math.exp(end)
    s=1j*lambda_w
    def outer_leg(p):
        # z^p*(1+c/z). The coefficient at z^(p-2) fixes c.
        c=(ang-p*(p-1))/(-2*nu*(p-1)**2+2j*w*(p-1))
        factor=np.exp(p*end)
        return [factor*(1+c/z),factor*(p+(p-1)*c/z)]
    a,b=np.linalg.solve(np.array([outer_leg(0.),outer_leg(s)]).T,[y,dx])
    impedance=1j*w+f(zb)*edge_x/(zb*edge)
    wronskian=w/abs(edge)**2
    assert abs(impedance.imag-wronskian)<2e-7*max(1,w)
    assert abs(abs(a)**2-abs(b)**2-1)<3e-6
    inertia=zb/math.sqrt(f(zb))
    omega2=f(zb)*(ell+.5)**2/zb**2
    chi=1/(inertia*(omega2-w*w)-impedance)
    boundary_to_early=chi*a/edge
    return a,b,impedance,chi,boundary_to_early,zb


def flat_factor(ell,s):
    return (-1)**(ell+1)*2**(-s)*math.prod((s+k)/(s-k) for k in range(1,ell+1))


def vaidya_rows():
    rows=[]
    for nu in (.02,.04,.055):
        lo,hi=horizon_radii(nu)
        for ell in (1,2,3):
            for w in (.035,.08,.19):
                a,b,m,chi,out,zb=transfer(nu,ell,w)
                a0,b0,*_=transfer(nu,ell,w,0)
                s=1j*w/nu
                # Both wings referred to physical scale M0/nu in affine u.
                phase=flat_factor(ell,s)/(nu*hi)**s
                target=math.exp(-math.pi*w/nu)/phase
                second=(target*a-b)/(np.conj(a)-target*np.conj(b))
                corrected=phase*(b+np.conj(a)*second)/(a+np.conj(b)*second)
                assert abs(corrected-math.exp(-math.pi*w/nu))<2e-14 and abs(second)<1.
                rows.append(dict(mass_loss=nu,ell=ell,similarity_frequency=w,
                                 inner_similarity_radius=lo,outer_similarity_radius=hi,
                                 surface_radius=zb,early_amplitude=abs(a),last_cone_amplitude=abs(b),
                                 signed_current_error=abs(abs(a)**2-abs(b)**2-1),
                                 outer_resolution_change=max(abs(a-a0),abs(b-b0)),
                                 surface_spectral_density=2*w*chi.imag/math.pi,
                                 outgoing_admittance_imag=m.imag,
                                 early_to_last_modulus=abs(b/a),
                                 affine_positive_frequency_ratio=math.exp(-math.pi*w/nu),
                                 needed_exterior_mode_modulus=abs(second)))
    return rows


def flat_energy_check():
    # Independent real-space test, using a decaying exponential times a polynomial in r.
    # For a decaying cone datum H(r)=r^p exp(-r), the flat dipole recurrence
    # for each new angular momentum l maps F to -F+2*l*x^l
    # * integral_x^infinity F(v)/v^(l+1) dv. Integer polynomial powers p>l
    # give an exact incomplete-gamma polynomial. Start on the cone at x=u/2.
    rows=[]
    for ell in (0,1,2,4):
        power=ell+3
        # To check several steps accurately, integrate the hierarchy of
        # antiderivatives backwards in log radius instead of reusing Mellin.
        def cone(x):
            return x**power*math.exp(-x)
        def cone_deriv(x):
            return (power/x-1)*cone(x)
        def eval_steps(x,z):
            pulse=-cone(x)
            derivative=-cone_deriv(x)
            slopes=[]
            for k,history in enumerate(z,1):
                # history = x^k integral_x^infty pulse(y)/y^(k+1) dy
                slope=(k*history-pulse)/x
                slopes.append(slope)
                pulse,derivative=-pulse+2*k*history,-derivative+2*k*slope
            return pulse,derivative,np.array(slopes)
        lo,hi=1e-5,85.
        if ell:
            def ode(x,z):
                return eval_steps(x,z)[2]
            sol=solve_ivp(ode,[hi,lo],np.zeros(ell),method="DOP853",dense_output=True,
                          rtol=4e-11,atol=1e-13)
            assert sol.success
        def out_energy(x):
            z=sol.sol(x) if ell else []
            return eval_steps(x,z)[1]**2/2
        incoming=quad(lambda x:(cone_deriv(x)**2+ell*(ell+1)*cone(x)**2/x**2)/2,lo,hi,
                      epsabs=1e-10)[0]
        outgoing=quad(out_energy,lo,hi,epsabs=1e-11,epsrel=2e-8)[0]
        error=abs(outgoing/incoming-1)
        assert error<4e-4
        # A smooth cone with zero energy near the vertex can radiate promptly
        # at u=0. The truncated energy omits that short initial interval.
        worst=0.
        for lam in (.1,1.,6.,15.):
            sq=abs(flat_factor(ell,.5+1j*lam))**2
            target=(lam**2+(ell+.5)**2)/(2*(lam**2+.25))
            worst=max(worst,abs(sq-target),abs(abs(flat_factor(ell,1j*lam))-1))
        assert worst<2e-13
        rows.append(dict(ell=ell,energy_on_cone=incoming,energy_reaching_future=outgoing,
                         truncated_relative_error=error,mellin_weight_error=worst))
    return rows


def exterior_angular_check():
    nu,w=.04,.12
    nodes,weights=roots_legendre(90)
    ells=range(1,6)
    def field(z):
        f=0j
        for l in ells:
            # Derivative of P_l(cos theta) supplies the meridional vector
            # harmonic. The magnetic partner rotates it by a right angle.
            deriv=-l*(eval_legendre(l-1,z)-z*eval_legendre(l,z))/math.sqrt(1-z*z)
            c=math.sqrt((2*l+1)/(l*(l+1)))*math.exp(-.16*l*(l+1))
            f+=c*deriv*transfer(nu,l,w)[4]
        return f
    values=np.array([field(z) for z in nodes])
    norm=float(weights @ abs(values)**2)
    smooth=float(-(weights @ ((1-nodes**2)*abs(values)**2))/(2*norm))
    hemi=-abs(field(0.))**2/(2*norm)
    dipole_hemi=-1/(2*(weights@(1-nodes**2)))
    dipole_smooth=-(weights@(1-nodes**2)**2)/(2*(weights@(1-nodes**2)))
    assert abs(dipole_hemi+3/8)<2e-14 and abs(dipole_smooth+2/5)<2e-14
    return dict(mass_loss=nu,similarity_frequency=w,cap_max_ell=5,
                single_dipole_hemisphere=dipole_hemi,single_dipole_smooth_quadrupole=dipole_smooth,
                scattered_hemisphere=hemi,scattered_smooth_quadrupole=smooth)


def spin_record():
    # Independently distributed generic angles with nonzero smooth spin
    # weights. These are conditional angular histories, not averages over a
    # specified astronomical object. The deterministic example uses binary
    # fractions so all helicity strings are distinguishable exactly.
    rows=[]
    a=-(2.**np.arange(12))/4096
    words=np.array(list(product((-1.,1.),repeat=12)))
    values=words@a
    plus=np.sum(words==1,axis=1)
    assert len(np.unique(values))==2**12
    p=np.zeros((2,len(plus)))
    for w,weight,k in ((0,1/8,0),(6,6/8,0),(12,1/8,0),(3,.5,1),(9,.5,1)):
        p[k,plus==w]=weight/math.comb(12,w)
    differences=[float((p[0]-p[1])@(values**k)) for k in range(5)]
    e4=sum(a[i]*a[j]*a[k]*a[h] for i in range(12) for j in range(i)
           for k in range(j) for h in range(k))
    assert max(abs(x) for x in differences[:4])<2e-15
    assert abs(differences[4]-24*18/55*e4)<2e-15
    # Lattice of possible J, convolved with the actual Gaussian resolution.
    # The squared Hellinger distance avoids subtracting two numbers near one.
    for sigma in (.00015,.001,.005,.025,.1,.3,1.,2.):
        grids=np.linspace(float(min(values))-9*sigma,float(max(values))+9*sigma,
                          max(2001,math.ceil(18*(max(values)-min(values)+18*sigma)/sigma)))
        keep=np.any(p>0,axis=0)
        densities=np.empty((2,len(grids)))
        v,prob=values[keep],p[:,keep]
        for start in range(0,len(grids),256):
            xs=grids[start:start+256]
            kernel=np.exp(-.5*((xs[:,None]-v[None,:])/sigma)**2)/(sigma*math.sqrt(2*math.pi))
            densities[:,start:start+256]=(kernel@prob.T).T
        integrate=getattr(np,"trapezoid")
        assert np.max(abs(integrate(densities,grids,axis=1)-1))<2e-9
        loss=float(integrate((np.sqrt(densities[0])-np.sqrt(densities[1]))**2,grids)/4)
        rows.append(dict(resolution=sigma,fidelity=1-loss,loss=loss,
                         broad_pointer_scaled_loss=loss*sigma**8))
    return dict(example_weights=a.tolist(),different_charge_words=len(np.unique(values)),
                moment_differences=differences,weak_pointer_coefficient=differences[4]**2/384,
                pointer_results=rows)


def tidal_capture_clock():
    # Maximum sum of reduced masses for disjoint two-ended links is a quarter
    # of their total mass. The angular or spatial span is a hypothesis here.
    light_speed=299792458.
    grav_constant=6.67430e-11
    hbar=6.62607015e-34/(2*math.pi)
    solar_mass=1.98847e30
    sensor_mass=1.31e-9
    radius_factor=1.05
    start_to_readout=1.3
    rows=[]
    for span in (1e-10,1e-4):
        kinetic_moment=sensor_mass*span**2/4
        critical=(kinetic_moment*light_speed**3*(1-start_to_readout**-1.5)
                  /(12*math.pi*grav_constant*hbar*radius_factor**1.5))
        for mass_solar in (3.,4e6,1e9):
            gm=grav_constant*mass_solar*solar_mass
            readout=2*radius_factor*gm/light_speed**2
            # The time left to the classical singularity fixes the tidal clock.
            remaining=2*readout**1.5/(3*math.sqrt(2*gm))
            earlier=remaining*start_to_readout**1.5
            tide=quad(lambda s:2/(9*s**2),remaining,earlier,epsabs=0.,epsrel=1e-12)[0]
            budget=kinetic_moment*tide/(4*hbar)
            ratio=critical/(mass_solar*solar_mass)
            assert abs(budget/(math.pi*ratio/2)-1)<3e-14
            rows.append(dict(hole_solar_masses=mass_solar,grain_mass_kg=sensor_mass,
                             link_span_m=span,critical_solar_masses=critical/solar_mass,
                             integrated_tide_inverse_seconds=tide,angle_upper_bound=budget,
                             trace_distance_upper_bound=math.sin(min(budget,math.pi/2)),
                             optimal_false_decision_lower_bound=(1-math.sin(min(budget,math.pi/2)))/2))
    return rows


def late_mass_and_pointer():
    # The dipole waveform has an independent closed form for cone D=r^4 e^-r.
    def pulse_slope(x):
        poly=x**4-2*x**3-4*x**2-4*x
        return math.exp(-x)*(4*x**3-6*x**2-8*x-4-poly)
    cuts=(0.,.5,2.,5.,10.,25.)
    mass=[quad(lambda t:pulse_slope(t)**2/2,cut,np.inf,epsabs=1e-15)[0] for cut in cuts]
    assert abs(mass[0]-45/4)<6e-13 and all(x>y>0 for x,y in zip(mass,mass[1:]))
    # In units d=1, q_min=1, b=2. The middle readout has a smooth
    # plateau on each occupied interval. Opposite translations reset
    # the same pointer even for coherent superpositions of many charges.
    def pointer(x):
        return math.sqrt(8/3)*math.sin(math.pi*x)**2 if 0<x<1 else 0.
    def slope(x):
        return math.sqrt(8/3)*math.pi*math.sin(2*math.pi*x) if 0<x<1 else 0.
    def switch(x):
        if x<=1:return 0.
        if x>=2:return 1.
        s=x-1
        return s*s*(3-2*s)
    def flag(x):
        return math.sin(math.pi*switch(x)/2)
    charges=(0.,1.,1.06,1.4,2.)
    norms=[quad(lambda x:pointer(x)**2*flag(x+2*q)**2,0,1)[0] for q in charges]
    post=[quad(lambda x:pointer(x)**2*flag(x+2*q)*flag(x+2*s),0,1)[0]
          for q in charges[1:] for s in charges[1:]]
    min_overlap=min(post)
    kinetic=quad(lambda x:slope(x)**2/2,0,1)[0]
    assert abs(kinetic-2*math.pi**2/3)<1e-12
    assert abs(norms[0])<1e-15 and max(abs(v-1) for v in norms[1:]+post)<2e-14
    lapse=math.sqrt(1-1/1.05)
    return dict(flat_cut_in_units_of_2L=list(cuts),remaining_mass_in_units_of_inverse_L=mass,
                pointer_positive_flag_probability=norms,pointer_test_charges=list(charges),
                smallest_coherent_reset_overlap=min_overlap,pointer_kinetic_in_units_hbar2_over_md2=kinetic,
                stationary_clock_budget_ns=lapse*730.,example_processing_ns=110.)


def radial_backreaction():
    # Radius and retarded time in units of the dipole profile length L.
    # The master solution is the regular dipole obtained by differentiating
    # a spherical wave. A series at the centre avoids subtracting O(1/r).
    from numpy.polynomial import Polynomial
    from scipy.optimize import minimize_scalar
    polys=[Polynomial((0.,0.,2.,2.,1.))]
    for _ in range(11):
        polys.append(polys[-1].deriv()-polys[-1])
    def derivative(u,k):
        x=u/2
        return 0. if x>650 else 2**(1-k)*math.exp(-x)*polys[k](x)
    def field(u,r):
        if r<.04:
            val,du,dr=0.,0.,0.
            for k in range(2,9):
                scale=2**k*(1-k)*r**(k-1)/math.factorial(k+1)
                val+=r*scale*derivative(u,k+1)
                du+=r*scale*derivative(u,k+2)
                dr+=k*scale*derivative(u,k+1)
            return val,du,dr
        v=u+2*r
        diff=derivative(v,0)-derivative(u,0)
        val=-derivative(u,1)-derivative(v,1)+diff/r
        du=-derivative(u,2)-derivative(v,2)+(derivative(v,1)-derivative(u,1))/r
        dr=-2*derivative(v,2)+2*derivative(v,1)/r-diff/r**2
        return val,du,dr
    def mass_density(u,r):
        value,_,slope=field(u,r)
        return (slope**2+2*(value/r)**2)/2
    def mass(u,r):
        return quad(lambda x:mass_density(u,x),0,r,epsabs=1e-10,epsrel=5e-10)[0]
    def lapse(u):
        return -quad(lambda x:field(u,x)[2]**2/x,0,np.inf,epsabs=1e-10)[0]
    def cut_mass(u):
        return quad(lambda v:derivative(v,2)**2,u,np.inf,epsabs=1e-12)[0]
    rows=[]
    for u in (0.,.7,2.,8.):
        m_inf=mass(u,np.inf)
        bondi=cut_mass(u)
        assert abs(m_inf-bondi)<5e-10
        for r in (1.,4.,9.):
            value,du,dr=field(u,r)
            flux=du**2-du*dr
            step=2e-5
            derivative_mass=(mass(u+step,r)-mass(u-step,r))/(2*step)
            assert abs(derivative_mass+flux)<4e-8
            rows.append(dict(retarded_time=u,radius=r,enclosed_mass=mass(u,r),
                             mass_at_infinity=m_inf,independent_future_flux=bondi,
                             local_mass_balance_error=abs(derivative_mass+flux)))
    peak=minimize_scalar(lambda x:-2*mass(0,x)/x,method="bounded",bounds=(1.,12.))
    central_lapse=lapse(0.)
    assert abs(central_lapse+75/16)<5e-10
    return dict(dipole_constraint_tests=rows,last_cone_lapse_at_centre=central_lapse,
                sampled_peak_radius=float(peak.x),sampled_peak_compactness=float(-peak.fun))


def active_mass_constraints():
    # Independent local-coordinate check during mass loss. At fixed physical
    # r we differentiate a real Vaidya multipole rather than the last-cone
    # waveform. The null dust has T_uu = nu/(4*pi*r^2).
    nu,ell,w=.04,2,.19
    ang=ell*(ell+1)
    def f(z):
        return 1-2/z-2*nu*z
    def ode(z,y):
        return [y[1],(ang*y[0]/z**2-(2/z**2-2*nu+2j*w)*y[1])/f(z)]
    sol=solve_ivp(ode,[3.,8.5],[.7+.2j,-.3+.4j],method="DOP853",
                  rtol=8e-14,atol=2e-15,dense_output=True)
    assert sol.success
    def local(u,r):
        mass=-nu*u
        z=r/mass
        y,dy=sol.sol(z)
        phase=np.exp(1j*w*math.log(mass)/nu)
        wave=(phase*y).real
        dr=(phase*dy/mass).real
        du=(phase*(-1j*w*y+nu*z*dy)/mass).real
        lapse=1-2*mass/r
        return (lapse*dr**2+ang*wave**2/r**2)/2,du**2-lapse*du*dr,dr**2/r
    records=[]
    for u in (-25.,-20.,-15.):
        for z in (3.4,5.1,7.8):
            r=-u*nu*z
            def deriv(fn,x):
                step=5e-5*max(1.,abs(x))
                return (-fn(x+2*step)+8*fn(x+step)-8*fn(x-step)+fn(x-2*step))/(12*step)
            e_u=deriv(lambda t:local(t,r)[0],u)
            j_r=deriv(lambda x:local(u,x)[1],r)
            required=nu*local(u,r)[2]
            error=abs(e_u+j_r-required)
            assert error<2e-8
            records.append(dict(retarded_time=u,radius=r,mass_loss=nu,
                                bare_flux_divergence=e_u+j_r,dust_lapse_term=required,
                                corrected_local_balance_error=error))
    return records


def singlet_recovery():
    # Angular Hilbert space of two distinguishable wave-packet legs of an
    # identical boson. The code uses equal helicities and two dipoles in J=0.
    angular=np.fliplr(np.diag([1.,-1.,1.]))/math.sqrt(3)
    raising=np.diag([math.sqrt(2.),math.sqrt(2.)],-1)
    jx=(raising+raising.T)/2
    jy=(raising-raising.T)/(2j)
    jz=np.diag([-1.,0.,1.])
    singlet_error=max(np.linalg.norm((np.kron(j,np.eye(3))+np.kron(np.eye(3),j))
                                     @angular.ravel()) for j in (jx,jy,jz))
    assert singlet_error<1e-14
    codes=np.zeros((2,6,6))
    for h in range(2):
        codes[h,3*h:3*h+3,3*h:3*h+3]=angular
        density=codes[h]@codes[h].T
        blocks=density[:3,:3]+density[3:,3:]
        assert np.max(abs(blocks-np.eye(3)/3))<1e-14
    cross=np.linalg.norm(codes[0]@codes[1].T)
    assert cross==0.
    def rotate(m,h,c):
        return (1-c*c)/2 if m==0 else (1+m*h*c)**2/4
    rows=[]
    for c1,c2 in ((.5,-.25),(-.7,.45),(.3,.6)):
        spin=-(2-c1*c1-c2*c2)/2
        states=[]
        for h in (-1,1):
            js=np.array([m*(c1-c2)+h*spin for m in (-1,0,1)])
            probs=np.array([rotate(m,h,c1)*rotate(-m,h,c2) for m in (-1,0,1)])
            states.append((js,probs/probs.sum()))
        def fidelity(key):
            weights={}
            for code_index,(js,probs) in enumerate(states):
                for v,prob in zip(js,probs):
                    weights.setdefault(round(key(v),12),np.zeros(2))[code_index]+=prob
            return (1+sum(math.sqrt(a*b) for a,b in weights.values()))/2
        sign=fidelity(np.sign)
        magnitude=fidelity(abs)
        assert abs(magnitude-1)<1e-14 and abs(fidelity(float)-.5)<1e-14
        rows.append(dict(polar_cosines=[c1,c2],unsigned_fidelity=magnitude,
                         sharp_signed_flux_fidelity=fidelity(float),sign_bit_fidelity=sign,
                         plus_charge_values=states[1][0].tolist(),plus_probabilities=states[1][1].tolist()))
    assert np.max(abs(np.array(rows[0]["plus_probabilities"])-np.array([1.,20.,25.])/46))<1e-14
    return dict(angular_singlet_error=singlet_error,cross_one_photon_density_norm=cross,
                angular_histories=rows)


def affine_check():
    # Regular positive-affine-frequency current g(u)=(1+i*u)^(-2).
    early=quad(lambda u:1/(1+u*u)**2,-np.inf,0)[0]
    nu=.04
    def similarity_power(t):
        mass=math.exp(-nu*t)
        du=-mass/nu
        return mass/(1+du**2)**2
    pulled=quad(similarity_power,-1100.,1100.,epsabs=1e-12)[0]
    assert abs(early-pulled)<1e-11
    return dict(early_affine_energy=early,late_affine_energy=early,
                pulled_back_early_energy=pulled,
                stationary_hawking_temperature_ratio=4*nu)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=ROOT/"verification"/"evaporating-exterior-memory-results.json")
    out=parser.parse_args().output
    result=dict(transfer=vaidya_rows(),flat=flat_energy_check(),angular=exterior_angular_check(),
                spin=spin_record(),affine=affine_check(),capture=tidal_capture_clock(),
                endpoint_and_flag=late_mass_and_pointer(),backreaction=radial_backreaction(),
                active_mass_balance=active_mass_constraints(),singlet=singlet_recovery())
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    print(out.name)
