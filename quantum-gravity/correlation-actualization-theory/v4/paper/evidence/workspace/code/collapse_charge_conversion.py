"""Spherical charge formation and four-dimensional conversion of a Dirac field."""
import argparse
import json
from math import atanh, cos, cosh, exp, pi, sin, sinh, sqrt, tanh
from pathlib import Path

import numpy as np
from scipy.integrate import cumulative_trapezoid, quad, simpson, solve_ivp
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq
from scipy.special import expit

ROOT = Path(__file__).resolve().parents[1]
G = 6.67430e-11
C_LIGHT = 299792458.
SOLAR_GM = 1.3271244e20


def uniform_star(compactness=.75):
    """PG dust time and areal lengths in units of r_s; comoving ball has radius one."""
    root = sqrt(compactness)
    radius = 1/compactness
    focus = 2*radius/(3*root)
    rph = 1.5
    phase_time = focus*((rph/radius)**1.5-1)
    reach = 2/root*(sqrt(rph/radius)-1)
    distance = max(0., min(2., reach))
    causal_outer_mass = 1-max(0., 1-distance)**3
    isotropic = 3*distance/4-distance**3/16
    via_null = quad(lambda t:1/(radius*(1-t/focus)**(2/3)),-phase_time,0.)[0]
    # Integrate independent parallel chords in a uniform comoving ball.
    chord = 1.5*quad(lambda b:b*min(distance,2*sqrt(1-b*b)),0,1,
                      points=[sqrt(1-(distance/2)**2)])[0]
    assert abs(via_null-reach)<1e-13 and abs(chord-isotropic)<2e-11
    return dict(compactness=compactness, radius=radius, dust_focus_after_birth=focus,
                wall_speed_inside=-root/2, wall_speed_outside=root,
                photon_sphere_to_surface_PG=phase_time,
                degree_outer=-1, degree_inner=1,
                isotropic_reach_from_photon_sphere=distance,
                max_causally_accessible_mass_fraction=causal_outer_mass,
                isotropic_escaping_fraction=isotropic,
                earliest_radius_for_center=radius*(1+root/2)**2,
                earliest_radius_for_all_directions=radius*(1+root)**2,
                time_needed_for_center=focus*((1+root/2)**3-1),
                time_needed_for_all_directions=focus*((1+root)**3-1),
                seconds_per_rs_three_solar=6*SOLAR_GM/C_LIGHT**3,
                fall_photon_sphere_to_singularity=2*rph**1.5/3)


def smooth_star(n, compactness=.75, initial_scale=2.8):
    """A regular, initially untrapped LTB profile with increasing shell-focus time."""
    c = compactness
    root = sqrt(c)
    def mass(u):
        return .5*(u/(1+u))**(3/n)
    def focusing(u):
        return (2/3)*initial_scale**1.5*(1+u)**(3/(2*n))
    def crossing(u):
        return focusing(u)-4*mass(u)/(3*c**1.5)
    def k(u):
        return (initial_scale*c)**1.5*(1+u)**(9/(2*n))*u**(1-3/n)
    def label(target):
        return brentq(lambda u:k(u)-target,1e-15,1e4,xtol=8e-15)
    u_fold, u_in, u_out = map(label,[2,(2-root)/(1+root),(2+root)/(1-root)])
    u_probe = 2*u_out
    assert u_in < u_fold < u_out < u_probe
    def radius(t,u):
        return ((3/2)*sqrt(2*mass(u))*(focusing(u)-t))**(2/3)
    def finite_difference_velocity(u):
        t = crossing(u)
        du = u*2e-5
        xr = (radius(t,u+du)-radius(t,u-du))/(2*du)
        dtdu = (crossing(u+du)-crossing(u-du))/(2*du)
        return xr/dtdu
    for u in [u_in,u_out,u_probe]:
        assert abs(radius(crossing(u),u)-2*mass(u)/c)<3e-13
        assert abs(finite_difference_velocity(u)+root*(1+k(u))/(2-k(u)))<2e-6
    return dict(edge_exponent=n, initial_scale=initial_scale,
                max_initial_compactness=(4/27)**(1/n)/initial_scale,
                first_pair_time=crossing(u_fold), birth_radius=2*mass(u_fold)/c,
                central_focus=focusing(0), inner_timelike_time=crossing(u_in),
                outer_timelike_time=crossing(u_out), inner_timelike_label=u_in,
                fold_label=u_fold, outer_timelike_label=u_out, probe_label=u_probe,
                probe_hit_time=crossing(u_probe), lead_after_outer_timelike=crossing(u_probe)-crossing(u_out),
                mass_fraction_at_probe=2*mass(u_probe))


def material_doublet():
    sx=np.array([[0,1],[1,0]],dtype=complex)
    sy=np.array([[0,-1j],[1j,0]],dtype=complex)
    sz=np.diag([1.,-1.])
    pauli=np.array([sx,sy,sz])
    axes=np.eye(3)
    chern=[]
    # Gauge-independent overlap products for the eight oriented faces.
    for band in [0,1]:
        total=0.
        for a in [-1.,1.]:
            for b in [-1.,1.]:
                for c in [-1.,1.]:
                    pts=[a*axes[0],b*axes[1],c*axes[2]]
                    if a*b*c<0: pts[1],pts[2]=pts[2],pts[1]
                    u=[np.linalg.eigh(np.einsum("i,ijk->jk",n,pauli))[1][:,band] for n in pts]
                    total+=np.angle(np.vdot(u[0],u[1])*np.vdot(u[1],u[2])*np.vdot(u[2],u[0]))
        chern.append(total/(2*pi))
    assert np.max(np.abs(np.array(chern)-[-1,1]))<1e-14
    rows=[]
    init=np.array([1,1],dtype=complex)/sqrt(2)
    other=np.array([1,-1],dtype=complex)/sqrt(2)
    for h in [.4,1.,2.,4.]:
        for exact in [False,True]:
            def rhs(t,vec):
                ham=(h/2)*(sx*cos(t)+sy*sin(t))+(sz/2 if exact else 0.)
                return -1j*ham@vec
            ans=solve_ivp(rhs,(0.,2*pi),init,method="DOP853",rtol=1e-11,atol=1e-13)
            measured=abs(np.vdot(other,ans.y[:,-1]))**2
            expected=0. if exact else sin(pi*sqrt(1+h*h))**2/(1+h*h)
            assert ans.success and abs(measured-expected)<1e-10
            rows.append(dict(twice_gap_over_omega=h,transport_term=exact,leakage=measured))
    return dict(signed_chern=chern,circuit=rows)


def absorbing_dust_surface():
    # r_s=1, G=1, the stellar surface has comoving radius 1.
    compactness=1/sqrt(2)
    speed=sqrt(compactness)
    nu=1/sqrt(1-speed**2)
    final_radius=1/compactness
    launch_radius=9*final_radius/4
    signal_radius=(3/speed+1)**2/4
    def scale(t):
        return (launch_radius**1.5-1.5*t)**(2/3)
    duration=2*(launch_radius**1.5-final_radius**1.5)/3
    def rates(t,state):
        a=scale(t)
        chi=state[0]
        radius=a*chi
        density=3/(8*pi*a**3)
        material_speed=speed-radius/a**1.5
        tension=nu*speed/(4*pi*a**1.5)
        area=4*pi*radius**2
        delta_mass=area*density*speed
        work=tension*8*pi*radius*material_speed
        return [speed/a,delta_mass,nu*delta_mass,work]
    traj=solve_ivp(rates,(0.,duration),[0.]*4,rtol=2e-12,atol=1e-14)
    assert traj.success
    chi,rest_mass,wall_frame_energy,area_work=traj.y[:,-1]
    sigma_area=nu*compactness*final_radius
    assert abs(chi-1)<1e-11 and abs(rest_mass-.5)<5e-12
    assert abs(sigma_area-wall_frame_energy-area_work)<2e-10
    assert abs(area_work-nu*rest_mass)<5e-12
    z=1/nu
    strength=compactness/z
    def potential(x):
        return 1-compactness/x-(nu-.5*strength*(x+x**-2))**2
    freq=2*compactness-compactness**2/(4*(1-compactness))
    h=3e-5
    assert abs(potential(1))<1e-14 and abs((potential(1+h)-potential(1-h))/(2*h))<1e-8
    assert abs((potential(1+h)+potential(1-h)-2*potential(1))/(2*h*h)-freq)<4e-7
    # A profile with slightly delayed outer shell focus. Use m proportional
    # to x^3 and t_s(x)-t_s(0) proportional to x^2, evaluated at one shell.
    departures=[]
    for lag in [1e-5,.001,.05]:
        time_ratio=1+lag
        proper_rapidity=nu*speed*time_ratio**2*(1+4*lag/(3*time_ratio))
        local_s=.12
        residual=sqrt(1+proper_rapidity**2)-nu-local_s*(proper_rapidity-nu*speed*time_ratio)
        bound=(speed-local_s)*(proper_rapidity-nu*speed)
        assert 0<bound<residual
        departures.append(dict(relative_focus_delay=lag,normal_constraint_residual=residual,lower_bound=bound))
    response=[]
    for fraction in [.95,1.,1.05]:
        hit=(sqrt(fraction*signal_radius)-.5*(1+1/speed))**2
        response.append(dict(relative_emission_radius=fraction,edge_compactness=1/hit,
                             areal_speed_at_edge=speed-1/sqrt(hit)))
    return dict(star_mass=.5,edge_radius=final_radius,speed=speed,intrinsic_reference=nu,
                signal_start_star_radius=signal_radius,wall_start_star_radius=launch_radius,
                traversal_time=duration,all_dust_intercepted=rest_mass,wall_frame_dust_energy=wall_frame_energy,
                pressure_work=area_work,final_material_energy=sigma_area,pressure_after_over_density=-.25,nonuniform_clock_test=departures,
                dimensionless_radial_frequency_squared=freq,sensitivity=response)


def shift_symmetric_sweep():
    # Dust comoving coordinate x has m(x)=x^3/2. The center focuses at t=0.
    # The calibrated signal travels in from the outer edge before the material
    # surface starts. Integrating in shell label also resolves the finite tip.
    cs=1/sqrt(2)
    stop=sqrt(cs)
    seed=atanh(stop)-stop
    nu=cosh(seed)
    def velocity(s,lock):
        return s if lock and s>=stop else tanh(seed+s)
    expansion=quad(lambda s:1/(velocity(s,False)+s/2),0.,stop)[0]
    initial_scale=exp(expansion)/cs
    send=(sqrt(initial_scale)+.5)**2
    def run(lag,start_factor):
        def geometry(x,t):
            left=lag*x*x-t
            if left<=0:
                raise ValueError("Shell focusing precedes the causal front")
            scale=(1.5*left)**(2/3)
            rx=scale*(1+4*lag*x*x/(3*left))
            return x*scale,rx,x/sqrt(scale)
        edge_time=lag-2*(send*start_factor)**1.5/3
        ray=solve_ivp(lambda x,t:[-geometry(x,t[0])[1]],(1.,0.),[edge_time],
                      rtol=1e-11,atol=1e-12)
        def cap_rhs(x,t):
            _,rx,s=geometry(x,t[0])
            return [rx/velocity(s,True)]
        def threshold(x,t):
            return geometry(x,t[0])[2]-stop
        front=solve_ivp(cap_rhs,(0.,1.),ray.y[:,-1],events=threshold,
                        dense_output=True,rtol=3e-12,atol=1e-13,max_step=.008)
        assert ray.success and front.success
        radius,_,s=geometry(1.,front.y[0,-1])
        maxres=0.
        for x in np.linspace(.001,1.,180):
            r,rx,sx=geometry(x,front.sol(x)[0])
            if sx>=1: raise ValueError("The candidate reached trapped dust")
            q,w=(cosh(seed+sx),sinh(seed+sx)) if sx<stop else (1/sqrt(1-sx*sx),sx/sqrt(1-sx*sx))
            f=q*(1+sx*sx/2)-w*sx-nu
            fp=sx*sx/2
            maxres=max(maxres,abs(nu-(q*fp-f)-(q-sx*w)),abs(r*fp-x**3/2))
        roots=front.t_events[0]
        mass_lock=roots[0]**3 if len(roots) else None
        if mass_lock is not None:
            assert abs(radius-mass_lock/cs)<3e-8
        assert maxres<1.e-12
        return dict(focus_delay=lag,relative_emission_radius=start_factor,central_receipt=ray.y[0,-1],
                    edge_time=front.y[0,-1],edge_radius=radius,edge_compactness=s*s,
                    mass_fraction_at_lock=mass_lock,max_constraint_residual=maxres)
    rows=[run(lag,fac) for lag in [0.,.03,.10] for fac in [.98,1.,1.02]]
    # At simultaneous homogeneous matching two equations fix the radius
    # without anticipating the future. Timing offsets change the edge mass.
    assert abs(rows[1]["edge_radius"]-1/cs)<1e-9
    assert cs/(2*(1-cs))>1 and abs((1-cs)*cs/(2*(1-cs))-cs/2)<1e-15
    return dict(bare_clock_sound_speed_squared=cs/(2*(1-cs)),projected_clock_sound_speed_squared=cs/2,
                seed_rapidity=seed,seed_speed=tanh(seed),intrinsic_reference=nu,
                static_compactness=cs,homogeneous_launch_scale=initial_scale,
                homogeneous_signal_scale=send,cases=rows)


def smooth_step(x):
    if x<=0:
        return 0.,0.
    if x>=1:
        return 1.,0.
    h = expit(1/(1-x)-1/x)
    # Evaluate the upper-tail derivative from the complementary logistic.
    dh = h*expit(1/x-1/(1-x))*(1/(1-x)**2+1/x**2)
    return h, dh


def mass_ratio(x):
    h, _ = smooth_step(x)
    return cos(pi*h/2)**2


I2 = np.eye(2, dtype=complex)
SX = np.array([[0,1],[1,0]],dtype=complex)
SZ = np.diag([1.,-1.]).astype(complex)
ODD = (I2-SX)/2


def check_full_spinor(k, mass_t, relative_winding):
    # All generators use dimensionless time x=t/T and momentum k=|p|T.
    def hamiltonians(x):
        h,dh = smooth_step(x)
        d, dd = relative_winding*h, relative_winding*dh
        v = I2 + np.expm1(-1j*pi*d)*ODD
        m1 = mass_t*cos(pi*d/2)**2
        diag = np.diag([m1,mass_t-m1])
        full = np.kron(I2,k*SX) + np.kron(v@diag@v.conj().T,SZ) + pi*dd*np.kron(ODD,I2)
        return full, k*SX+m1*SZ
    initial = np.vstack((I2,np.zeros((2,2),complex)))
    def rhs(x,vector):
        full,single = hamiltonians(x)
        return np.r_[(-1j*full@vector[:8].reshape(4,2)).ravel(),
                     (-1j*single@vector[8:].reshape(2,2)).ravel()]
    sol = solve_ivp(rhs,(0.,1.),np.r_[initial.ravel(),I2.ravel()],
                    method="DOP853",rtol=3e-11,atol=2e-13)
    assert sol.success
    full = sol.y[:8,-1].reshape(4,2)
    expected = sol.y[8:,-1].reshape(2,2)
    chosen = 0 if relative_winding==0 else 2
    error = np.linalg.norm(full[chosen:chosen+2]-expected,ord=2)
    leakage = np.linalg.norm(full[2-chosen:4-chosen],ord=2)**2
    assert error < 2e-9 and leakage < 2e-19
    return dict(kT=k, massT=mass_t, relative_winding=relative_winding,
                correct_channel_amplitude_error=error, unwanted_channel_norm2=leakage)


def quench_spectrum(z, mass_t, steps):
    # Propagate both helicities via their identical, normalized two-component problems.
    gamma = np.arctan2(z,mass_t)
    a,b = np.cos(gamma/2).astype(complex),np.sin(gamma/2).astype(complex)
    dt = 1/steps
    for j in range(steps):
        m = mass_t*mass_ratio((j+.5)*dt)
        freq = np.hypot(z,m)
        phase = np.cos(freq*dt)
        factor = -1j*dt*np.sinc(freq*dt/pi)
        a,b = phase*a+factor*(m*a+z*b), phase*b+factor*(z*a-m*b)
    return abs(a-b)**2/2


def work_and_spectrum(mass_t):
    z = np.linspace(0.,110.,1101)
    probability = quench_spectrum(z,mass_t,1600)
    comparison = quench_spectrum(z,mass_t,800)
    def energy(freq,prob):
        return (2/pi**2)*simpson(freq*z*z*prob,x=z)
    energy_massless = energy(z,probability)
    energy_massive = energy(np.hypot(z,mass_t),probability)
    coarse = energy(z,comparison)
    limit = z<=80
    truncated = (2/pi**2)*simpson(z[limit]**3*probability[limit],x=z[limit])
    def phase(x):
        return 2*quad(mass_ratio,x,1.,epsabs=5e-12)[0]*mass_t
    slope = cos(mass_t)/mass_t + 2*quad(lambda x: sin(phase(x)),0.,1.,epsabs=1e-10)[0]
    small = np.array([.0002,.0004])
    small_prob = quench_spectrum(small,mass_t,1600)
    measured = float(np.mean((1-2*small_prob)/small))
    assert abs(measured-slope)<1e-5 and abs(probability[0]-.5)<1e-11
    assert abs(coarse-energy_massless)/energy_massless<6e-5
    assert abs(truncated-energy_massless)/energy_massless<2e-4
    temp = 1/(2*slope)
    points = np.array([.5,1.,2.,4.,8.])
    spec = quench_spectrum(points*temp,mass_t,1600)
    fermi = expit(-points)
    return dict(initial_mass_times_duration=mass_t, inverse_slope_temperature_T=temp,
                relative_energy_to_Fermi_at_slope=energy_massless/(7*pi**2*temp**4/60),
                massless_energy_times_T4=energy_massless, massive_energy_times_T4=energy_massive,
                two_step_energy_relative_error=abs(coarse-energy_massless)/energy_massless,
                cutoff_energy_relative_change=abs(truncated-energy_massless)/energy_massless,
                analytic_twice_negative_slope=slope, direct_twice_negative_slope=measured,
                energy_over_slope_temperature=list(points), population=list(spec),
                ideal_Fermi_population=list(fermi))


def exponential_readout():
    # Set the bulk rate lambda to one; this sets the energy unit, independently
    # of any black-hole mass. The early and late joins are C-infinity.
    heavy, light = 120., .0005
    tgrid = np.linspace(0.,1.,3001)
    start_area = cumulative_trapezoid([smooth_step(t)[0] for t in tgrid],tgrid,initial=0.)
    primitive = CubicSpline(tgrid,start_area)
    entry = heavy*exp(-.5)
    cut = 1+np.log(entry/light)
    def gap(t):
        if t<1: return heavy*exp(-float(primitive(t)))
        if t<=cut: return entry*exp(1-t)
        return light*exp(cut-t)*(1-smooth_step(t-cut)[0])
    rows = []
    for k in [.10,.35,.7,1.,1.5,2.]:
        theta = np.arctan2(k,heavy)
        spinor = np.array([cos(theta/2),sin(theta/2)],complex)
        for lo,hi in [(0.,1.),(1.,cut),(cut,cut+1)]:
            ans=solve_ivp(lambda t,y:-1j*(k*SX+gap(t)*SZ)@y,(lo,hi),spinor,
                          method="DOP853",rtol=6e-11,atol=5e-13)
            assert ans.success
            spinor=ans.y[:,-1]
        n = abs(spinor[0]-spinor[1])**2/2
        fermi=expit(-2*pi*k)
        bound = np.arctan(k/entry)+light
        assert abs(n-fermi)<bound
        rows.append(dict(momentum_over_rate=k,capped_probability=n,
                         infinite_exponential_probability=fermi,error_bound=bound))
    return dict(start_gap_over_rate=heavy,end_of_exponential_gap_over_rate=light,
                duration_times_rate=cut+1,frequencies=rows)


def moving_clock():
    # Outgoing Vaidya, G=1. Compare the material acceleration to parallel
    # transport with the actual Bondi-time lapse on a regular timelike track.
    u=np.linspace(0.,1.,501)
    M=.2-.025*u
    R=1+.03*u+.005*u*u
    rp=.03+.01*u
    F=1-2*M/R
    p=np.sqrt(F+2*rp)
    ru=.05/R
    rr=2*M/R**2
    pp=(ru+rr*rp+.02)/(2*p)
    gamma_uu_u=-rr/2
    gamma_uu_r=(ru+F*rr)/2
    Uu,Ur=1/p,rp/p
    au=-pp/p**3+gamma_uu_u*Uu**2
    ar=.01/p**2-rp*pp/p**3+gamma_uu_r*Uu**2+rr*Uu*Ur
    # n_mu=(-R',1)/p in the (u,r) chart.
    measured=ar-rp*au
    # p*a = a^r - R' a^u; the direct covariant calculation above
    # includes the change of the normalization of the normal frame.
    transport=pp/p+M/R**2
    assert max(abs(measured-transport))<1e-13
    q=1/p
    radius_velocity=rp/p
    d=p-radius_velocity
    qdot=-pp/p**3
    dynamic_residuals=[max(abs(d-(1/q-radius_velocity))),
                       max(abs(R*((1-1/q**2)/2+radius_velocity/q)-M)),
                       max(abs(R*measured/p+d-((q+1/q)/2-R*qdot/q)))]
    assert max(dynamic_residuals)<1e-13

    # A shrinking constant-compactness track with finite-time M^nu decay,
    # and a finite-radius cap ending at large outward boost. No integration
    # to machine zero is needed for the improper-integral tests.
    cs=1/sqrt(2)
    nu=2/3
    k=.01
    ms=np.array([1.,.3,.1,.03])
    lapse=np.sqrt(1-cs-4*k*ms**nu/cs)
    log_amp=2*(np.log(lapse[0]/lapse) - cs**2/(4*k*nu)*(ms**(-nu)-1))
    assert np.all(np.diff(log_amp)<0)
    # At R_f finite a power-law amplitude x^alpha needs alpha<1 for w=2.
    # The squared switch rate near the endpoint then scales as x^(alpha-2).
    alpha=.75
    cutoffs=np.array([.01,.0001,1e-6])
    integrated_work=(cutoffs**(alpha-1)-1)/(1-alpha)
    proper_exponent=1.5*alpha-1
    proper_work=(1-cutoffs**proper_exponent)/proper_exponent
    assert np.all(np.diff(integrated_work)>0) and np.all(proper_work<1/proper_exponent)
    return dict(moving_emission_energy_charge_pressure_error=dynamic_residuals,proper_time_quadratic_cost_to_cutoffs=list(proper_work),
                proper_time_quadratic_cost_limit=1/proper_exponent,bosonic_weight=2,matched_compactness=cs,
                matched_radius_over_rs=1/cs,boost_rate_relative_error=max(abs(measured-transport)),
                conventional_lapse_rate_over_kappa=.5,photon_orbit_rate_over_kappa=4/(3*sqrt(3)),
                constant_compactness_masses=list(ms),constant_compactness_log_gain=list(log_amp),
                terminal_exponent=alpha,cutoffs=list(cutoffs),quadratic_control_divergence=list(integrated_work))


def finite_cap():
    # Pressureless expanding shell, d tau=du in units G=c=1.  A
    # distribution of remaining flight lengths provides the positive mass flux.
    R0,M0,ell=1.,.2055,.13
    def survive(s): return (2-s)**2*(4+s)/16
    def primitive(s): return s-3*s*s/8+s**4/64
    def evaluate(s):
        mass=M0*survive(s)
        radius=sqrt(R0**2+2*M0*ell*primitive(s))
        transport=(R0/radius)**2
        ratio=survive(s)*R0/radius
        depletion=smooth_step(ratio)[0]
        return mass,radius,transport,transport*depletion
    final=evaluate(2.)
    assert abs(quad(survive,0.,2.)[0]-.75)<1e-12 and final[-1]==0.
    assert abs(final[1]**2-R0**2-1.5*M0*ell)<1e-13
    # Slopes on the open interval and step at the start; a smooth compact
    # initial distribution also removes this initial luminosity jump.
    for s in [.15,.6,1.1,1.8]:
        b=evaluate(s)
        ds=1e-5
        rdot=(evaluate(s+ds)[1]-evaluate(s-ds)[1])/(2*ds*ell)
        assert abs(rdot-b[0]/b[1])<3e-9
    return dict(initial_radius=R0,initial_mass=M0,cell_radius=ell,duration=2*ell,
                final_radius=final[1],final_mass=final[0],geometric_memory_remaining=final[2],
                final_effective_gap=final[-1],mean_flight_over_cell_radius=.75,
                history=[dict(flight_length=s,mass=evaluate(s)[0],radius=evaluate(s)[1],
                              relative_gap=evaluate(s)[3]) for s in [.0,.4,.8,1.2,1.6,2.]])


def covariant_channels():
    # Two distinguishable spinless incident particles and two distinguishable massless products.
    m1,m2=1.,3.
    def v(s):
        return sqrt((1-(m1+m2)**2/s)*(1-(m1-m2)**2/s))
    threshold=(m1+m2)**2
    def psi(s):
        return exp(-(s-threshold)/8)*(1+.3j*sin(s))
    norm=quad(lambda s:v(s)*abs(psi(s))**2,threshold,200.,epsabs=1e-11)[0]
    outgoing=quad(lambda s:abs(sqrt(v(s))*psi(s))**2,threshold,200.,epsabs=1e-11)[0]
    assert abs(norm-outgoing)<1e-11
    a,b=.05,1.
    strength=1/sqrt(a*b)
    def prob(vv): return 4*strength*vv/(1+strength*vv)**2
    assert abs(prob(a)-prob(b))<1e-13
    return dict(invariant_weighted_norm=norm,radiation_norm=outgoing,
                least_contact_probability=prob(a), range_of_phase_space_factor=[a,b],
                optimal_contact_squared=strength)


def capture_and_emission_pressure():
    # Compare the angular Einstein equation with the radius variation of
    # the expansion term. Static holding is tested at nonzero incoming
    # dust flux and for a complete outgoing Vaidya mass history.
    radius=1.6
    nu=1.0743749507336
    accretion_error=[]
    for compactness in [.71,.75,.82,.9]:
        s=sqrt(compactness)
        q=1/sqrt(1-compactness)
        w=q*s
        density=.003
        # Independent spherical LTB acceleration: H_parallel from R_t=-s.
        h_parallel=-4*pi*radius*density/s+s/(2*radius)
        eta_dot=4*pi*radius*density*q**3
        a_normal=eta_dot+h_parallel*w
        qdot=w*eta_dot
        required=radius*a_normal+1/q-nu
        baseline=(q+1/q)/2-nu
        accretion_error.append(abs(required-baseline-radius*w/q**2*qdot))
    output=[]
    mass0=.5
    for u in np.linspace(0.,1.,251):
        mass=mass0*(1-u)**2*(1+2*u)
        derivative=-6*mass0*u*(1-u)
        q=1/sqrt(1-2*mass/radius)
        qdot=derivative*q**4/radius
        a_normal=q*mass/radius**2-derivative*q**3/radius
        luminosity_density=-derivative/(4*pi*radius**2)
        angular=radius*a_normal+1/q-nu
        material=(q+1/q)/2-nu-radius*qdot/q
        stored=radius*(1-1/q**2)/2
        output.append((abs(angular-material),abs(mass-stored),
                       abs(derivative+4*pi*radius**2*luminosity_density*q/q)))
    errors=np.max(output,axis=0)
    assert max(accretion_error)<1e-13 and max(errors)<2e-14
    return dict(incoming_pressure_error=max(accretion_error),
                radiating_pressure_error=errors[0],mass_charge_error=errors[1],
                flux_error=errors[2],sampled_retarded_times=len(output),
                terminal_mass=mass,terminal_clock=q,terminal_radius=radius)


def vary_surface_action():
    # Check the clock, lapse and area variations of the action before using
    # a gravitational constraint. The independent variables here are the
    # material lapse, the radius history and the pullback of the dust clock.
    time=np.linspace(0.,1.,601)
    lapse=1+.1*time
    radius=1+.08*time+.03*time**2
    rt=.08+.06*time
    q=1.95+.13*time
    rate=lapse*q
    bump=16*time**2*(1-time)**2
    bump_dt=32*time*(1-time)*(1-2*time)
    eps=3e-5
    values=[]
    for sector in ["receiving","emitting"]:
        def impulse(x):
            if sector=="receiving":
                return -np.arccosh(x)+np.sqrt(1-x**-2)
            return np.log(x)
        gp=-np.sqrt(q*q-1)/q**2 if sector=="receiving" else 1/q
        def action(l,r,rprime,tprime):
            x=tprime/l
            integrand=l*r*(x+1/x)/2+r*rprime*impulse(x)
            return simpson(integrand,x=time)
        fd=[]
        for dl,dr,drt,dtprime in [(bump,0.,0.,0.),(0.,0.,0.,bump_dt),(0.,bump,bump_dt,0.)]:
            plus=action(lapse+eps*dl,radius+eps*dr,rt+eps*drt,rate+eps*dtprime)
            minus=action(lapse-eps*dl,radius-eps*dr,rt-eps*drt,rate-eps*dtprime)
            fd.append((plus-minus)/(2*eps))
        number=radius*((1-q**-2)/2+rt/lapse*gp)
        density=radius*((q+1/q)/2)-q*number
        pressure=lapse*(q+1/q)/2-radius*gp*.13
        source=[simpson(density*bump,x=time),simpson(number*bump_dt,x=time),
                simpson(pressure*bump,x=time)]
        error=float(np.max(np.abs(np.array(fd)-source)))
        assert error<2e-8
        values.append(dict(sector=sector,max_variation_error=error))
    return values


def late_scalar_return():
    # At first Born order a positive outgoing monopole seeds an ingoing wave
    # far from the star. Once the star is gone the regular center returns it.
    # Normalize the pulse duration to one and use a weak early mass.
    early_mass=.01
    def weighted_pulse(s):
        return early_mass*s*s*(1-s)**4
    moment=quad(weighted_pulse,0.,1.)[0]
    assert abs(moment-early_mass/105)<1e-17
    rows=[]
    for retarded_time in [4.,10.,40.,100.]:
        def derivative(u):
            return 4*quad(lambda s:weighted_pulse(s)/(u-s)**3,0.,1.)[0]
        slope=derivative(retarded_time)
        # Integrate the remaining energy with t=retarded_time/u, so that
        # the endpoint at infinity corresponds to a regular finite limit.
        def residual_flux(t):
            u=retarded_time/t
            return 4*pi*derivative(u)**2*retarded_time/t**2
        energy=quad(residual_flux,0.,1.,epsabs=1e-26)[0]
        lower=64*pi*moment**2/(5*retarded_time**5)
        assert slope>=4*moment/retarded_time**3 and energy>=lower
        rows.append(dict(u=retarded_time,amplitude_derivative=slope,
                         late_energy=energy,ratio_to_leading_bound=energy/lower))
    assert 1<rows[-1]["ratio_to_leading_bound"]<1.03
    return dict(weighted_pulse_integral=moment,late_return=rows)


def render(path, births, spectra):
    import matplotlib.pyplot as plt
    fig,(a,b)=plt.subplots(1,2,figsize=(8.8,3.25),layout="constrained")
    p=np.array([s["edge_exponent"] for s in births])
    for key, label, st in [("first_pair_time","First charged cut","o-"),
                            ("outer_timelike_time","Outer cut becomes timelike","s--"),
                            ("probe_hit_time","Test shell arrives","^:")]:
        a.plot(p,[s[key] for s in births],st,label=label,ms=4)
    a.set_xscale("log",base=2)
    a.set_xticks(p,labels=[str(i) for i in p])
    a.set(xlabel="Density edge exponent",ylabel=r"Dust time $c t/r_s$")
    a.legend(frameon=False,fontsize=8)
    for s in spectra:
        b.semilogy(s["energy_over_slope_temperature"],s["population"],"o-",
                   label=r"$mT=%g$"%s["initial_mass_times_duration"],ms=3)
    xx=np.linspace(.5,8,100)
    b.semilogy(xx,expit(-xx),"k--",label="Fermi distribution")
    b.set(xlabel=r"Energy / low-frequency temperature",ylabel="Mode occupation")
    b.legend(frameon=False,fontsize=8)
    fig.savefig(path)
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    births=[smooth_star(n,1/sqrt(2)) for n in [4,8,16,32,64]]
    spectra=[work_and_spectrum(m) for m in [.5,2.,6.]]
    report=dict(units="collapse r_s=1; field hbar=c=1 with time measured in switching durations",
                uniform=[uniform_star(1/sqrt(2)),uniform_star(.75),uniform_star(8/9)],smooth=births,
                doublet=material_doublet(), sweeping=absorbing_dust_surface(), shift_symmetric=shift_symmetric_sweep(), spinors=[check_full_spinor(k,m,w) for k,m in [(0.,.5),(1.,2.),(3.,6.)] for w in [-1,0,1]],
                spectra=spectra, recoil=covariant_channels(), optical=exponential_readout(), clock=moving_clock(), cap=finite_cap(), late_scalar=late_scalar_return(), pressure=capture_and_emission_pressure(), variations=vary_surface_action(),
                half_band_min_L_over_rs=(9*pi/4)**(1/3)*4*pi/5)
    (ROOT/"verification/collapse-charge-conversion-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    if args.figure:
        render(args.figure,births,spectra)
    print("Four-dimensional collapse and radiation checks passed.")
    print("Locally exchanged spectrum / thermal energy at same slope:",
          [round(s["relative_energy_to_Fermi_at_slope"],5) for s in spectra])
