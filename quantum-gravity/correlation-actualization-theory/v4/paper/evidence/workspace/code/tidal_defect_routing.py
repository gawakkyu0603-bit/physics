"""Finite fall, shear winding and a two-species conformal radiation calculation."""
import argparse
import json
from math import asin, cos, cosh, log, pi, sin, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import hyp0f1

ROOT = Path(__file__).resolve().parents[1]
G = 6.67430e-11
LIGHT = 299792458.
GAMMA = 2.
BETA = sqrt(3) / 2
CENTRAL = 2.


def infall(mass, body_radius, bias=1e-9):
    amplitude = 3 * G * mass * GAMMA**2 * (1 + BETA**2)
    length = (.004 * amplitude / bias)**(1/3)
    rim = .2 * length
    duration = pi * rim / LIGHT
    peak = (2/3) / (5/3)**2.5
    birth_height = (amplitude * peak / bias)**(1/3)
    last_height = 4 * length - GAMMA * BETA * LIGHT * duration
    assert 4*length > birth_height > last_height > body_radius

    def tide(s, arm=1):
        # H is the longitudinal separation in the rest coordinates of the body.
        z = length * (2 - .2*np.cos(pi*s) + arm*1j*.2*np.sin(pi*s))
        H = 4*length - s*GAMMA*BETA*LIGHT*duration
        return bias - amplitude*z**2 / (abs(z)**2 + H**2)**2.5

    times = np.linspace(0, 1, 4001)
    # Return along the second physical history in reverse parameter order.
    closed = np.r_[tide(times), tide(times[::-1], -1)[1:]]
    degree = (np.unwrap(np.angle(closed))[-1] - np.angle(closed[0])) / (2*pi)
    margin = min(abs(closed))/bias
    assert np.isclose(degree, -1) and tide(0).real > 0 > tide(1).real
    assert np.all(np.imag(tide(times[1:-1])) < 0)
    assert np.all(np.imag(tide(times[1:-1], -1)) > 0)
    # Compare an ordinary material receiver localized to the same ball. This
    # bounds only the stated differential shear Hamiltonian during the read.
    hbar = 1.054571817e-34
    receiver_mass = 4*pi*2500.*rim**3/3
    min_detector_mass = pi*hbar/(8*bias*rim**2*duration)
    open_time = (last_height-body_radius)/(GAMMA*BETA*LIGHT)  # half locally / lapse 1/2
    derivative_norm = quad(lambda x:(6*x-6*x*x)**2,0,1)[0]
    assert abs(derivative_norm-6/5)<1e-13
    return dict(mass_kg=mass, proper_radius_m=body_radius, bias_per_s2=bias,
                retarded_ramp_duration_s=open_time, preparation_energy_J=pi*hbar*derivative_norm/(4*open_time),
                test_receiver_mass_kg=receiver_mass, orthogonal_read_min_mass_kg=min_detector_mass,
                tidal_angle_bound_rad=4*receiver_mass*rim**2*bias*duration/hbar,
                read_radius_m=rim, proper_read_time_s=duration,
                time_to_front_after_read_s=(last_height-body_radius)/(GAMMA*BETA*LIGHT),
                time_from_birth_to_front_s=(birth_height-body_radius)/(GAMMA*BETA*LIGHT),
                start_shear_over_bias=tide(0).real/bias, end_shear_over_bias=tide(1).real/bias,
                sampled_min_shear_over_bias=margin, winding=round(degree),
                inverse_read_time_Hz=1/duration)


def binary_test():
    # Two equally heavy separated spheres, d=1, with a common longitudinal H.
    def shear(x,y,H):
        return sum((x-a+1j*y)**2/((x-a)**2+y*y+H*H)**2.5 for a in (-1,1))
    result = []
    for H in (1., 2., 3.):
        dz = 1e-5
        dx = (shear(dz,1.,H)-shear(-dz,1.,H))/(2*dz)
        dy = (shear(0.,1.+dz,H)-shear(0.,1.-dz,H))/(2*dz)
        determinant = dx.real*dy.imag - dx.imag*dy.real
        # At y=d the imaginary x derivative equals 4*(H^2-3)/(H^2+2)^(7/2).
        exact = 16*(H*H-3)/(2+H*H)**6
        assert abs(shear(0,1,H)) < 1e-15 and np.isclose(determinant, exact, rtol=1e-8)
        result.append(dict(H_over_d=H,jacobian=determinant,degree=int(np.sign(determinant))))
    return result


def length_for_blend(a):
    return sqrt(CENTRAL/3) * (sqrt(2*a)+(a+2)*asin(sqrt(a/(a+2))))/2


def switch_shape(r, a):
    if r <= -a:
        return r, 1., 0., 0.
    if r >= a:
        return 0., 0., 0., length_for_blend(a)
    weight = (a-r)/(2*a)
    log_factor = -(a-r)**2/(4*a)
    norm = sqrt(a*a + 2*a)
    def primitive(x):
        return (x*sqrt(norm**2-x*x) + norm**2*asin(x/norm))/(4*a)
    length = sqrt(CENTRAL/3) * (primitive(r)-primitive(-a))
    return log_factor, weight, sqrt(CENTRAL/3)*sqrt(weight*(1-weight)+1/(2*a)), length


def radiating_history(distance=pi, hawking_time=128., cutoff_mass=.3):
    # Time in units of initial inverse surface gravity; masses in units of initial mass.
    # The overall normalization then gives the initial incident-vacuum Hawking flux.
    cut_time = hawking_time*(1-cutoff_mass**3)
    tail_time = 9*hawking_time*cutoff_mass**3
    end = cut_time + tail_time

    def relative_flux(u):
        if u<0 or u>end:
            return 0.
        if u<cut_time:
            return (1-u/hawking_time)**(-2/3)
        return ((end-u)/tail_time/cutoff_mass)**2

    def riccati(u, y):
        return (y[1], relative_flux(u)/4 - y[1]**2)

    def solution(start, finish):
        out = solve_ivp(riccati,(start,finish),(0.,0.),rtol=2e-11,atol=2e-13,
                        dense_output=True,max_step=.25)
        assert out.success
        return out.sol

    left, right = solution(0., end), solution(end, 0.)
    # An independent, mass-local implementation uses only an autonomous emission
    # law and the regular vacuum. No retarded-time endpoint is fed to this lookup.
    coeff = 3*hawking_time/4
    power = 2/3
    cap_k = 1/(3*hawking_time*cutoff_mass**(2+power))
    p = 2-power
    def cap_branch(m):
        arg = coeff*m**p/(cap_k*p*p)
        amplitude = hyp0f1(1/p,arg)
        momentum = coeff*m*hyp0f1(1+1/p,arg)
        return np.array([log(amplitude),momentum/amplitude])
    def mass_riccati(m,y):
        flux = 1/(3*hawking_time*m*m)
        return y[1]/flux, coeff-y[1]**2/flux
    mass_sol = solve_ivp(mass_riccati,(cutoff_mass,1.),cap_branch(cutoff_mass),
                         dense_output=True,rtol=2e-12,atol=2e-13,max_step=.01)
    assert mass_sol.success
    def mass_at(u):
        if u<=cut_time:
            return (1-u/hawking_time)**(1/3)
        return cutoff_mass*((end-u)/tail_time)**3
    def mass_right(u):
        m = mass_at(u)
        a0,v0 = cap_branch(m) if m<=cutoff_mass else mass_sol.sol(m)
        return np.array([a0,-v0])
    mass_check = max(float(np.max(np.abs(mass_right(u)-right(u)))) for u in np.linspace(0,end,251))
    assert mass_check < 2e-7
    def ratio(u):
        return left(u)[0]-right(u)[0]

    a = brentq(lambda h:length_for_blend(h)-distance,.0001,10.)
    assert ratio(0.) < -a and ratio(end) > a
    start = brentq(lambda u:ratio(u)+a,0.,end)
    stop = brentq(lambda u:ratio(u)-a,0.,end)
    turn = brentq(ratio,start,stop)
    def fields(u):
        l, wl = left(u)
        b, wr = right(u)
        r = l-b
        log_factor, t, density, arc = switch_shape(r,a)
        w = t*wl+(1-t)*wr
        # rho''/rho includes the derivative of the blending weight.
        dt = -1/(2*a) if -a < r < a else 0.
        rho_curvature = relative_flux(u)/4 + (dt-t*(1-t))*(wl-wr)**2
        speed = density*(wl-wr)
        return b+log_factor, w, speed, rho_curvature, arc

    grid = np.unique(np.r_[np.linspace(0,end,851), np.linspace(start,stop,441)])
    residual = max(abs(4*(v[3]+3*v[2]**2/CENTRAL)-relative_flux(u))
                   for u in grid for v in [fields(u)])
    integration_points = sorted({start,stop,cut_time})
    recovered_mass = quad(relative_flux,0.,end,points=integration_points)[0]/(3*hawking_time)
    twist_cost = quad(lambda u:fields(u)[2]**2,start,stop,epsabs=1e-10)[0]
    integrated_speed = quad(lambda u:fields(u)[2],start,stop,epsabs=1e-10)[0]
    assert abs(recovered_mass-1) < 2e-11 and residual < 2e-11
    assert abs(integrated_speed-distance) < 2e-9
    for boundary in (0.,end):
        assert np.linalg.norm(fields(boundary)[:2]) < 1e-11
    # A separate finite difference uses only the assembled redshift and phase.
    direct = []
    for u in (start-.3, .8*start+.2*stop, turn, .2*start+.8*stop,stop+.3, (end+cut_time)/2):
        eps = .00025
        l0, lm, lp = [fields(t)[0] for t in (u,u-eps,u+eps)]
        geometric = (np.expm1(lp-l0)+np.expm1(lm-l0))/eps**2
        twist = (fields(u+eps)[4]-fields(u-eps)[4])/(2*eps)
        direct.append(abs(4*(geometric+3*twist**2/CENTRAL)-relative_flux(u)))
    assert max(direct)<.0004
    # For a fixed generator, port 1 input has visible norm sin^2(relative_angle/2)
    # in port 2. This is a single-output diagnostic; both outgoing species are invertible.
    gr = np.array([[u,relative_flux(u),*fields(u)] for u in grid])
    return dict(initial_kappa_times_hawking_lifetime=hawking_time,
                cutoff_mass_fraction=cutoff_mass, terminal_time=end, switch_log_ratio_halfwidth=a,
                switch_start=start,switch_stop=stop, equal_solutions_at=turn,
                max_log_redshift_amplitude=float(np.max(gr[:,2])),
                min_ray_derivative=float(np.exp(-2*np.max(gr[:,2]))),
                mass_emitted=recovered_mass, integrated_group_speed=integrated_speed,
                integrated_speed_squared=twist_cost, max_flux_formula_error=residual,
                max_finite_difference_flux_error=max(direct),
                mass_local_profile_max_abs_error=mass_check,
                final_log_amplitude=fields(end)[0],final_log_slope=fields(end)[1]), gr


def early_budget():
    local_time_over_rs = .053892704185277064
    local_lapse = .5
    kappa_times_retarded = .5*local_time_over_rs/local_lapse
    return {kind:12*distance_sq/(CENTRAL*kappa_times_retarded**2)
            for kind,distance_sq in (("bare_swap_excess_over_Hawking",pi*pi),
                                     ("phase_adjusted_excess_over_Hawking",pi*pi/2))}


def terminal_circle():
    # One complex fermion takes the *entire* two-port benchmark terminal power.
    # The proper circumference is one initial inverse surface-gravity light time.
    t_h, s, delta = 128., .30, 1.
    end = 9*t_h*s**3
    level, central = 2., 1.
    angle = 2*pi*sqrt(24*level/central-1)
    def g(u):
        return .5*((end-u)/(end*s))**2
    def basis(start,finish,slope):
        sol = solve_ivp(lambda u,y: (y[1],g(u)*y[0]),(start,finish),(0.,slope),
                        rtol=2e-12,atol=5e-14,max_step=.1,dense_output=True)
        assert sol.success
        return sol.sol
    yl, yr = basis(0,end,1.), basis(end,0,-1.)
    size = yl(end)[0]
    assert abs(yr(0)[0]/size-1)<8e-11
    plus, minus = np.exp(angle/2), np.exp(-angle/2)
    def record(u):
        ll,ld = yl(u)
        rr,rd = yr(u)
        A,B = rr+plus*ll, rr+minus*ll
        la,lb = (rd+plus*ld)/A,(rd+minus*ld)/B
        pos = delta/angle*(np.log(A)-np.log(B))
        speed = delta/angle*(plus-minus)*size/(A*B)
        # y=(s')^-1/2 is proportional to sqrt(A B).
        geometry = g(u)-(la-lb)**2/4
        return pos,speed, geometry+(angle/(2*delta)*speed)**2
    grid = np.linspace(0.,end,901)
    profile = np.array([record(t) for t in grid])
    area = quad(lambda u:record(u)[1],0,end,epsabs=2e-11)[0]
    assert abs(area-delta)<5e-10
    assert np.max(abs(profile[:,2]-np.array([g(t) for t in grid])))<2e-9
    assert np.allclose(profile[[0,-1],0], [0.,delta],atol=1e-13)
    assert abs(profile[0,1]-profile[-1,1])<1e-12
    cutoffs = np.array([1e-2,1e-4,1e-6])
    # Integral of the end-to-end squared kernel, in circle coordinates
    # with both distances between epsilon and one in arbitrary short units.
    corner = np.log((1+cutoffs)**2/(4*cutoffs))
    return dict(level=level, circumference=delta, duration=end, projective_distance=angle,
                max_sample_read_speed=float(np.max(profile[:,1])), integrated_circle_length=area,
                endpoint_read_speed=profile[0,1], stress_max_abs_error=float(np.max(abs(
                    profile[:,2]-np.array([g(t) for t in grid])))),
                corner_cutoffs=list(cutoffs), corner_integrals=list(corner))


def delayed_output():
    # One passage per light-circulation time.  Orthogonal time bins stay
    # distinguishable when the early radiation is retained as a single system.
    sample_phases = (.15*pi, .64*pi, .89*pi)
    retained = np.eye(2, dtype=complex)
    emitted = []
    basis_twist = np.array([[1.,1.],[1.,-1.]])/sqrt(2)
    for angle in sample_phases:
        outgoing = 1j*sin(angle/2)*basis_twist@retained
        emitted.append(outgoing)
        retained = cos(angle/2)*retained
    early_survival = float(np.linalg.norm(retained,2)**2)
    emitted.append(basis_twist@retained)    # a final complete exchange on every ray
    isometry = np.concatenate(emitted)
    identity_error = np.linalg.norm(isometry.conj().T@isometry - np.eye(2),2)
    assert 0 < early_survival < 1 and identity_error < 2e-15
    return dict(pre_flush_survival=early_survival, final_memory_input_gain=0.,
                outgoing_gram_error=identity_error)


def plot(path, gr):
    import matplotlib.pyplot as plt
    fig, (a,b) = plt.subplots(1,2,figsize=(8.8,3.2),layout="constrained")
    u, f, lr, w, speed, geo, arc = gr.T
    a.plot(u,f,label="Total outgoing power",color="#285b72")
    a.plot(u,4*geo,"--",label="Redshift contribution",color="#9a4926")
    a.plot(u,12*speed**2/CENTRAL,":",label="Exchange contribution",color="#38363c")
    a.axhline(0,color=".7",lw=.6)
    a.set(xlabel=r"Retarded time $\kappa_i u$",ylabel="Power / initial Hawking power")
    a.legend(frameon=False,fontsize=8)
    b.plot(u,2*lr/log(10),color="#285b72",label=r"$-\log_{10}p'$")
    b.set(xlabel=r"Retarded time $\kappa_i u$",ylabel=r"Redshift $-\log_{10}p'$")
    b2=b.twinx()
    b2.plot(u,np.cos(arc/2)**2,"--",color="#9a4926",label="Swapped fraction")
    b2.set(ylabel="Fraction in exchange output",ylim=(-.06,1.08))
    b.legend(b.lines+b2.lines,[l.get_label() for l in b.lines+b2.lines],frameon=False,fontsize=8,loc="upper left")
    fig.savefig(path)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args = parser.parse_args()
    bare, graph = radiating_history()
    balanced, _ = radiating_history(pi/sqrt(2))
    report = dict(human=infall(70.,.85),grain=infall(1.31e-9,.00005),binary=binary_test(),
                  deadline=early_budget(),bare_exchange=bare,phase_adjusted=balanced, delay_loop=delayed_output(), single_port_terminal=terminal_circle())
    (ROOT/"verification/tidal-defect-routing-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    if args.figure:
        plot(args.figure, graph)
    print("Read time (s):", report["human"]["proper_read_time_s"],report["grain"]["proper_read_time_s"])
    print("Radiated mass fraction:",bare["mass_emitted"],"switch duration:",bare["switch_stop"]-bare["switch_start"])
