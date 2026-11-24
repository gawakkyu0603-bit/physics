"""Surface Dirac pairs, exterior scattering and clocks in a Schwarzschild approach.

All equations use c = hbar = k_B = 1. Schwarzschild lengths and asymptotic
times are in r_s, except for the explicitly labelled SI examples.
Run from the project or from the unmodified reproduction archive.
"""
from pathlib import Path
import json
import math

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import gammaln, loggamma

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "verification" / "fermionic-horizon-memory-results.json"
RS_SECONDS = 3 * 2 * 4.925490947641267e-6
LIGHT = 299792458.0


def impedance(p, ell, speed=1.0):
    """Finite-sphere vacuum impedance, with the planar coupling matched."""
    value = p / math.tanh(math.pi * p / (2 * speed))
    for angular in range(1, ell + 1):
        value = (p * p + (speed * angular) ** 2) / value
    return value


def susceptibility():
    rows = []
    for speed in (0.5, 1.0):
        for p in (0.13, 0.8, 2.5, 8.0):
            omega = 2 * speed
            n = np.arange(1, 40001, dtype=float)
            # The omitted positive tail lies between two integrals of a
            # decreasing function. This check does not use the coth identity.
            a = p / omega
            partial = float(np.sum(a*a / (n*n + a*a)))
            tail_low = a * math.atan(a / (n[-1] + 1))
            tail_high = a * math.atan(a / n[-1])
            scale = 2 * omega / math.pi
            lower = scale * (0.5 + partial + tail_low)
            upper = scale * (0.5 + partial + tail_high)
            value = impedance(p, 0, speed)
            assert lower - 1e-13 <= value <= upper + 1e-13
            angular_errors = []
            for ell in range(8):
                arg = complex((ell + 1) / 2, p / (2 * speed))
                gamma_value = 2 * speed * math.exp(2 * (loggamma(arg + 0.5) - loggamma(arg)).real)
                angular_errors.append(abs(impedance(p, ell, speed) / gamma_value - 1))
            assert max(angular_errors) < 1e-12
            rows.append(dict(speed=speed, p=p, K=value, spectral_interval=[lower, upper],
                             angular_relative_error=max(angular_errors)))
    echoes = []
    for z in (0.25, 0.75, 1., 1.6, 4.):
        rho = (1-z)/(1+z)
        n = np.arange(1, 81)
        echoes_n = -(1-rho*rho) * rho**(n-1)
        baseline = float(rho*rho + np.sum(echoes_n**2))
        error = max(abs(rho + np.sum(echoes_n * np.exp(-n * p * math.pi)) -
                        (p - z * impedance(p, 0)) / (p + z * impedance(p, 0)))
                    for p in (0.05, 0.2, 1.5))
        assert abs(baseline-1) < 5e-15 and error < 1e-14
        echoes.append(dict(z=z, prompt=rho, first_echo=float(echoes_n[0]),
                           energy=baseline, laplace_error=error))
    return dict(spectral_checks=rows, separated_echoes=echoes)


def finite_matter():
    thermal = []
    for x in (1., 2.8, 4., 6.):
        absorb = math.tanh(x/4)
        thermal.append(dict(omega_over_T=x, planar_absorptive_ratio=absorb,
                            planar_reflection_floor=((1-absorb)/(1+absorb))**2))
    gap = 8 * math.pi * (1/3) / (9/8)
    weights = []
    for pairs, k in ((20, 2), (20, 10), (200, 10), (20000, 10)):
        ratio = math.prod(1 - j/pairs for j in range(k))
        log_check = gammaln(pairs+1.) - gammaln(pairs-k+1.) - k*math.log(pairs)
        assert abs(math.exp(log_check) - ratio) < 3e-10
        weights.append(dict(pair_slots=pairs, quanta=k, norm_squared_over_bosonic=ratio))
    return dict(planar_thermal=thermal, gap_over_static_local_Hawking_T=gap,
                first_pair_Pauli_factor=math.tanh(gap/4), finite_occupancies=weights)


def schwarzschild_transmission(x, ell, stop):
    """Unit ingoing wave at the left port, plane-wave decomposition at stop.

    x = omega r_s, r_* = r + log(r-1). This is the exterior, cut off at
    r=9/8 and attached to a free radial channel on its left.
    """
    def rhs(r, state):
        f = 1 - 1/r
        potential = f * (ell*(ell+1)/r**2 + 1/r**3)
        psi, derivative = state
        return [derivative/f, (potential - x*x)*psi/f]

    sol = solve_ivp(rhs, (9/8, stop), [1.+0j, -1j*x], method="DOP853",
                    rtol=2e-10, atol=1e-11)
    if not sol.success:
        raise RuntimeError(sol.message)
    psi, derivative = sol.y[:, -1]
    incoming = (psi - derivative/(1j*x))/2
    outgoing = (psi + derivative/(1j*x))/2
    transmitted = float(1/abs(incoming)**2)
    reflected = float(abs(outgoing/incoming)**2)
    return transmitted, abs(transmitted + reflected - 1.0)


def exterior():
    rows = []
    for ell, x in ((0, 1/(4*math.pi)), (0, 0.22), (0, 0.5), (0, 1.),
                   (1, 0.22), (1, 0.5), (2, 0.5)):
        coarse, e0 = schwarzschild_transmission(x, ell, 600)
        fine, e1 = schwarzschild_transmission(x, ell, 1200)
        assert max(e0, e1) < 3e-8 and abs(coarse-fine) < 3e-5
        rows.append(dict(ell=ell, omega_rs=x, exterior_port_transmission=fine,
                         cutoff_difference=abs(fine-coarse), flux_error=max(e0, e1)))
    return rows


def inward_clock(r, energy):
    """Minus dv/dr along a freely falling particle, with its conserved energy."""
    k = math.sqrt(energy**2 - 1 + 1/r)
    return 1/(k*(energy+k))


def u_primitive(y):
    """Antiderivative for du/dy = -2 y^3/(y-1), r_s = 1, y>1."""
    return -2 * (y**3/3 + y**2/2 + y + math.log(y-1))


def v_primitive(y):
    return -2 * (y**3/3 - y**2/2 + y - math.log(y+1))


def transfer(y, delay):
    previous = y + delay/2
    return previous**3 * (y-1) / ((previous+1) * y**3)


def kappa(y, delay):
    previous = y + delay/2
    return ((y-1) * (3/previous - 1/(previous+1) - 3/y) + 1)/(2*y**3)


def clocks():
    receiver = []
    for cap, emission, energy in ((9/8, 1.5, 1.1), (9/8, 1.5, math.sqrt(2)),
                                 (1.5, 2.0, math.sqrt(2))):
        lead_advance = quad(inward_clock, cap, emission, args=(energy,))[0]
        rq = brentq(lambda r: quad(inward_clock, cap, r, args=(1.,))[0] - lead_advance,
                    cap, emission)
        yc, yq = math.sqrt(cap), math.sqrt(rq)
        proper_lead = 2/3 * (yq**3 - yc**3)
        angle = 2 * (yq-yc)
        proper_A = quad(lambda r: 1/math.sqrt(energy**2 - 1 + 1/r), 0, cap,
                        epsabs=1e-12)[0]
        receiver.append(dict(capture_R_over_rs=cap, emission_R_over_rs=emission,
                             E_A=energy, E_surface=1., charge_arrival_R_over_rs=rq,
                             charge_lead_surface_us=proper_lead*RS_SECONDS*1e6,
                             activation_angle=angle, causal_area_fraction=math.sin(angle/2)**2,
                             charge_to_capture_advanced_rs=lead_advance,
                             A_time_to_classical_singularity_us=proper_A*RS_SECONDS*1e6,
                             available_phase=2*(yc-1)))
    delay = math.pi
    peeling = []
    for y in (1.1, 1.01, 1.001, 1.0001):
        p = transfer(y, delay)
        h = (y-1)*1e-3
        numerical = -(math.log(transfer(y+h,delay))-math.log(transfer(y-h,delay))) / (
            u_primitive(y+h)-u_primitive(y-h))
        kval = kappa(y,delay)
        numerical_p = (v_primitive(y+delay/2+h)-v_primitive(y+delay/2-h))/(
            u_primitive(y+h)-u_primitive(y-h))
        assert abs(numerical-kval) < 2e-7 and abs(numerical_p/p-1) < 1e-6
        dy_du = -(y-1)/(2*y**3)
        kprime = (kappa(y+h,delay)-kappa(y-h,delay))/(2*h)*dy_du
        flux_ratio = (kval*kval+2*kprime)/0.25
        peeling.append(dict(y=y, incident_radius=(y+delay/2)**2, dv_du=p,
                            kappa_over_Hawking=2*kval, flux_over_Hawking=flux_ratio))
    arrest = []
    cap = 1.5
    for gap_y in (1e-2, 1e-4, 1e-8):
        yb = 1+gap_y
        lapse = math.sqrt((yb-1)*(yb+1))/yb
        remaining_phase = delay - 2*(math.sqrt(cap)-yb)
        proper_delay = yb**2 * remaining_phase
        arrest.append(dict(gap_y=gap_y, phase_after_arrest=remaining_phase,
                           release_after_arrest_proper_us=proper_delay*RS_SECONDS*1e6,
                           release_after_arrest_infinity_s=proper_delay*RS_SECONDS/lapse,
                           freefall_retarded_span_rs=u_primitive(yb)-u_primitive(math.sqrt(cap))))
    return dict(capture_episodes=receiver, freefall_peeling=peeling, arrest=arrest,
                earliest_origin_radius_for_horizon=(1+delay/2)**2,
                static_return_us=delay*(9/8)*RS_SECONDS*1e6,
                geodesic_photon_sphere_to_horizon_us=2/3*(1.5**1.5-1)*RS_SECONDS*1e6,
                geodesic_horizon_to_classical_singularity_us=2/3*RS_SECONDS*1e6)


def late_window():
    # A passive static ensemble has the same delay law for each input epoch.
    # Endpoints of the bin in which light reaches 1 < y < 1 + epsilon.
    records = []
    for yc in (math.sqrt(9/8), math.sqrt(1.5)):
        for width in (0.01, 0.0001):
            lower, upper = 2*(yc-1-width), 2*(yc-1)
            records.append(dict(capture_y=yc, late_gate_y_width=width,
                                allowed_delay=[lower, upper], fast_fraction_of_sphere=upper/math.pi,
                                mass_for_uniform_D_on_0_pi=(upper-lower)/math.pi))
    # Static proper gap ell near a Schwarzschild horizon: ell ~ 2 sqrt(r_s delta r).
    # Evaluate u differences using log(y-1) without rounding an astronomical 1+epsilon to one.
    rs_metres = RS_SECONDS*LIGHT
    planck = 1.616255e-35
    log_y_gap = 2*math.log(planck/rs_metres)-math.log(8)
    y_start = math.sqrt(1.5)
    span = -2*(1/3+1/2+1+log_y_gap) - u_primitive(y_start)
    ideal_fraction = (planck/rs_metres)**2 * span/(96*math.pi)
    return dict(passive_delays=records, three_solar_mass_rs_m=rs_metres,
                example_proper_clearance_m=planck, static_mass_span_rs=span,
                static_mass_span_ms=span*RS_SECONDS*1e3,
                ideal_one_channel_plateau_fraction=ideal_fraction)


def mobile_tip():
    """An autonomous conformal endpoint before recoil, and its finite-mass collision."""
    def phase(y):
        return -2*(y-1)
    wi0, wi1 = phase(math.sqrt(1.5)), phase(math.sqrt(9/8))
    yo0, yo1 = 1+1e-4, 1+1e-10
    wo0, wo1 = phase(yo0), phase(yo1)
    slope = (wo1-wo0)/(wi1-wi0)
    intercept = wo0 - slope*wi0
    beta = (1-slope)/(1+slope)
    a = intercept*(1+beta)/2
    sample = []
    for wi in np.linspace(wi0, wi1, 7):
        wm = (a+wi)/(1+beta)
        length = a-beta*wm
        wo = wm+length
        assert abs(wo-(slope*wi+intercept)) < 1e-15 and length > 0
        sample.append(dict(input_phase=float(wi), reflection_phase=float(wm),
                           output_phase=float(wo), length_at_reflection=float(length)))
    def past_y(y):
        return 1+(y-1+intercept/2)/slope
    def k_and_slope(y):
        yp = past_y(y)
        h = 3/yp-1/(yp+1)
        dh = -3/yp**2+1/(yp+1)**2
        b = h/slope-3/y
        numerator = 1+(y-1)*b
        deriv = (b+(y-1)*(dh/slope**2+3/y**2))/(2*y**3) - 3*numerator/(2*y**4)
        return numerator/(2*y**3), deriv * (-(y-1)/(2*y**3))
    radiation = []
    for delta in (1e-4, 5e-5, 1e-5, 1e-6, 1e-8, 1e-10):
        y = 1+delta
        kval, kd = k_and_slope(y)
        radiation.append(dict(y_minus_one=delta, input_radius_over_rs=past_y(y)**2,
                              kappa_over_H=2*kval, flux_over_H=4*(kval*kval+2*kd),
                              adiabaticity=abs(kd)/kval**2))
    loss = 0.01
    min_mass_per_E = 2*(1-loss)/(loss*math.sqrt(slope))
    kinetic_per_E = min_mass_per_E*(1-math.sqrt(slope))**2/(2*math.sqrt(slope))
    recoil = []
    for mass in (10., 1e3, min_mass_per_E, 1e6):
        k = math.sqrt(slope)
        initial_plus, initial_minus = mass*k, mass/k
        final_plus = initial_plus+2.
        final_minus = mass*mass/final_plus
        measured = (initial_minus-final_minus)/2.
        analytic = 1/(slope*(1+2/(mass*k)))
        assert abs(measured/analytic-1) < 1e-10
        recoil.append(dict(rest_mass_over_incoming_energy=mass, output_over_input=analytic,
                           fraction_of_fixed_speed_gain=slope*analytic))
    return dict(delay_map_slope=slope, conformal_speed=beta, gamma=(1+slope)/(2*math.sqrt(slope)),
                initial_intercept_a=a, events=sample, radiation=radiation,
                retarded_span_rs=u_primitive(yo1)-u_primitive(yo0),
                retarded_span_in_inverse_T=(u_primitive(yo1)-u_primitive(yo0))/(4*math.pi),
                min_kinetic_energy_over_input_for_one_percent=kinetic_per_E, recoil=recoil)


def tension_release(episode):
    """A signal at the mouth unpins a prestressed line at its far end.

    Use tension = 1 as a conformal energy unit. In the input null coordinate
    i, the exact forced problem is m dk/di = -tension*k^2 + 2*incident_flux.
    """
    q = -2*(math.sqrt(episode["charge_arrival_R_over_rs"])-1)
    i0, i1 = -2*(math.sqrt(1.5)-1), -2*(math.sqrt(9/8)-1)
    o0, o1 = -2e-4, -2e-10
    d0, d1 = i0-q, i1-q
    slope = (o1-o0)/(i1-i0)
    a = (slope*(d0+d1)+math.sqrt((slope*(d0+d1))**2+4*(1-slope)*slope*d0*d1))/(2*(1-slope))
    length = (o0-q-a*d0/(a+d0))/2
    o_q = q + 2*length
    def empty(i):
        d = i-q
        return a/(a+d), o_q + a*d/(a+d)
    k0, o_first = empty(i0)
    k1, o_last = empty(i1)
    assert max(abs(o_first-o0), abs(o_last-o1)) < 2e-16
    # Test the causal travelling trigger and the free accelerated trajectory at each reflection.
    onset = q+length
    for i in np.linspace(i0, i1, 13):
        k, o = empty(i)
        w = (i+o)/2
        x = length+a-math.hypot(a, w-onset)
        assert w > onset and x>0 and abs(x-(o-i)/2)<1e-14
        gamma = (1+k*k)/(2*k)
        assert abs((length-x)-a*(gamma-1)) < 1e-14

    def backreaction(fraction, integrate=False):
        energy = fraction*length
        intensity = energy/(i1-i0)
        equilibrium = math.sqrt(2*intensity)
        t = math.tanh(equilibrium*(i1-i0)/a)
        k = equilibrium*(k0+equilibrium*t)/(equilibrium+k0*t) if energy else k1
        o = o_first + a*(k0-k) + 2*energy
        shift = o-o_last
        assert -4e-16 <= shift <= 2*energy+4e-16
        error = 0.
        if integrate:
            def rhs(i, state):
                vel, out = state
                return [(2*intensity-vel**2)/a, vel**2]
            sol = solve_ivp(rhs,(i0,i1),[k0,o_first],method="DOP853",rtol=3e-12,atol=1e-15)
            if not sol.success:
                raise RuntimeError(sol.message)
            error = max(abs(sol.y[0,-1]-k),abs(sol.y[1,-1]-o))
            assert error<1e-12
        # For positive o the freefall continuation is only a failure diagnostic.
        return dict(energy_over_initial_tension_energy=fraction, final_k=k,
                    last_return_phase=o, extra_phase=shift, upper_bound=2*energy,
                    ODE_error=error)
    crit = brentq(lambda b:backreaction(b)["last_return_phase"],0,1e-5,xtol=1e-20)
    flux_rows = []
    # o(i) is fractional linear for zero load on the accelerating branch.
    # {V(i(o)),u} separates into the intrinsic Schwarzians and squared Jacobians.
    def sch_clock(y, sign):
        # clock_derivative is y^3/(y+sign) in phase w; scale r_s=1
        h = 3/y-1/(y+sign)
        dh = -3/y**2+1/(y+sign)**2
        return (dh-h*h/2)/4
    for o in np.geomspace(2e-4,2e-10,7)*-1:
        den = o_q+a-o
        i = q-a+a*a/den
        k = a/(a+i-q)
        y, yp = 1-o/2, 1-i/2
        o_u = (y-1)/y**3
        schwarz = o_u**2*(sch_clock(yp,1)/k**4-sch_clock(y,-1))
        flux_rows.append(dict(output_phase=float(o), input_R_over_rs=yp**2,
                              flux_over_H=-8*schwarz))
    correlators = []
    for end_gap in (1e-6, 1.1e-10):
        y_end = 1+end_gap
        for separation in (2., 6., 12., 22.):
            if u_primitive(y_end)-u_primitive(1+1e-4) < separation:
                continue
            start_gap = math.exp(brentq(
                lambda loggap: u_primitive(y_end)-u_primitive(1+math.exp(loggap))-separation,
                math.log(end_gap),math.log(1e-4),xtol=1e-13))
            # Use a subtraction-free gravitational travel-time difference for nearby points.
            def ray(gap):
                den = o_q+a+2*gap
                i = q-a+a*a/den
                yp = 1-i/2
                derivative = (yp**3/(yp+1))*(a/den)**2*gap/(1+gap)**3
                return den,yp,derivative
            de,ye,pe = ray(end_gap)
            ds,ys,ps = ray(start_gap)
            dy = a*a*(start_gap-end_gap)/(de*ds)
            dv = 2*(dy*((ys*ys+ys*ye+ye*ye)/3-(ys+ye)/2+1)-math.log1p(dy/(ye+1)))
            # Same two retarded instants in the thermal and ray-traced two-point functions.
            elapsed = 2*((start_gap-end_gap)*(
                ((1+start_gap)**2+(1+start_gap)*(1+end_gap)+(1+end_gap)**2)/3+
                (2+start_gap+end_gap)/2+1)+math.log(start_gap/end_gap))
            ratio = pe*ps/dv**2*(4*math.sinh(elapsed/4))**2
            correlators.append(dict(end_y_gap=end_gap, separation_rs=elapsed,
                                    vacuum_current_two_point_over_thermal=ratio))
    return dict(signal_phase=q, release_onset_phase=onset, initial_length=length,
                mass_over_tension=a, input_interval=[i0,i1], output_interval=[o0,o1],
                empty_endpoint_k=[k0,k1], critical_incident_energy_over_initial_tension_energy=crit,
                load_trials=[backreaction(f,True) for f in (0.,1e-12,1e-10,1e-8,1e-5,0.01)],
                vacuum_flux=flux_rows, finite_separation_correlators=correlators)


def quantum_recoil():
    """Null momenta q=E_m+p_m and Q after the collision. Invariant one-body
    measures are proportional to dlog(q) and dlog(E) for the right-moving photon.
    """
    mass = 7.0
    worst_inverse, worst_determinant = 0., 0.
    def forward(logs):
        q, e = np.exp(logs)
        return np.log([q+2*e, mass**2*e/(q*(q+2*e))])
    for q in (0.1, 1., 17.):
        for e in (0.03, 0.5, 22.):
            logs = np.log([q,e])
            Q, E = np.exp(forward(logs))
            restored = [mass**2*Q/(mass**2+2*E*Q), E*Q**2/(mass**2+2*E*Q)]
            worst_inverse = max(worst_inverse, float(np.max(np.abs(np.array(restored)/[q,e]-1))))
            h = 1.e-5
            jac = np.column_stack([(forward(logs+h*v)-forward(logs-h*v))/(2*h)
                                   for v in np.eye(2)])
            worst_determinant = max(worst_determinant, abs(float(np.linalg.det(jac))-1))
    assert worst_inverse < 1e-13 and worst_determinant < 1e-9
    # In ordinary q and E prepare independent uniforms on [3,5], [elo,ehi].
    def density(Q, elo, ehi):
        length = max(0., min(5.,Q-2*elo)-max(3.,Q-2*ehi))
        return length/(4*(ehi-elo))
    rows = []
    for e0 in (1.02, 1.7, 2.3):
        one, two = (1.,1.04), (e0,e0+0.04)
        edges = sorted({q+2*e for band in (one,two) for e in band for q in (3.,5.)})
        pair = lambda Q: math.sqrt(density(Q,*one)*density(Q,*two))
        overlap = sum(quad(pair,a,b,epsabs=1e-12)[0] for a,b in zip(edges,edges[1:]))
        rows.append(dict(first_band=one, second_band=two, root_overlap=overlap))
    assert rows[-1]["root_overlap"] == 0.
    return dict(momentum_inverse_relative_error=worst_inverse,
                invariant_jacobian_error=worst_determinant, finite_energy_bands=rows)


def terminal_decay():
    """Two correlated rays from one outward massive decay in a fixed exterior.

    The floor is the limiting fixed radius for a direct ray without any
    further encounter. The calculation is geometric optics, not a greybody
    probability for thermal-frequency wave packets.
    """
    bc2 = 27/4
    def escape(r, floor, energy=1.):
        f = (r-1)/r
        beta = math.sqrt(1-f/energy**2)
        if r < 1.5:
            c = math.sqrt(max(0.,1-bc2*f/r**2))
            # Ratios of light-cone velocities avoid subtracting two numbers near 1.
            cone = bc2/(r*(1+c))**2
            boost = 1/(energy*(1+beta))**2
            fraction = max(0.,(cone-boost)/(cone+boost))
        else:
            turn = max(1.5,floor)
            c = -math.sqrt(max(0.,1-(turn/r)**2*f/(1-1/turn)))
            fraction = max(0.,(beta-c)/(1-beta*c))
        return beta,c,min(1.,fraction)
    rows = []
    for floor in (1+1.e-8,9/8,1.5,16/7):
        for r in (floor, floor+0.5):
            beta,cut,prob = escape(r,floor)
            u = (np.arange(100000)+0.5)/100000
            mu_a,mu_b = (beta+u)/(1+beta*u),(beta-u)/(1-beta*u)
            sample = float(np.mean((mu_a>cut)&(mu_b>cut)))
            assert abs(sample-prob)<1.1e-5
            rows.append(dict(floor_over_rs=floor, decay_radius_over_rs=r,
                             both_escape_rays=prob, angular_check=sample,
                             boost_cost_from_infall_in_rest_masses=2/((r-1)/r)-1))
    delays = []
    for floor in (9/8,16/7):
        for width in (0.05, 1., 30.):
            def probability(z):
                r = (floor**1.5+1.5*z/width)**(2/3)
                return math.exp(-z)*escape(r,floor)[2]
            corner = max(0.,width*2/3*(1.5**1.5-floor**1.5))
            answer = quad(probability,0,40,points=[corner] if 0<corner<40 else [],
                          epsabs=3e-11)[0]
            delays.append(dict(floor_over_rs=floor, decay_width_times_rs=width,
                               direct_pair_fraction=answer, tail_bound=math.exp(-40)))
    return dict(near_horizon_both_escape_limit=23/31, examples=rows,
                waiting_time_averages=delays, eikonal_only=True)


def maxwell_outlet():
    """Continuum weights in the *physical* fixed exterior after reflection.
    The master-field intensity is not a two-photon axion decay rate.
    """
    wall, source = 9/8, 1.4
    rows = []
    for ell in (1,2):
        for x in (1/(4*math.pi),3/(4*math.pi),5/(4*math.pi)):
            def rhs(r,state):
                f = 1-1/r
                pot = f*ell*(ell+1)/r**2
                psi,der,even,deven = state
                return [der/f,(pot-x*x)*psi/f,deven/f,(pot-x*x)*even/f]
            sol = solve_ivp(rhs,(wall,1500),[0.,1.,1.,0.],t_eval=[source,750,1500],
                            method="DOP853",rtol=3e-10,atol=1e-12)
            if not sol.success:
                raise RuntimeError(sol.message)
            weights = []
            for j in (0,2):
                intensity = [sol.y[j,0]**2/(sol.y[j,n]**2+(sol.y[j+1,n]/x)**2)
                             for n in (1,2)]
                weights.append(dict(intensity=intensity[1], cutoff_difference=abs(intensity[1]-intensity[0])))
            assert all(w["cutoff_difference"]<1e-5 for w in weights)
            rows.append(dict(ell=ell, omega_over_Hawking_T=x*4*math.pi,
                             Dirichlet=weights[0], Neumann=weights[1]))
    B = 3.
    def pot(r):
        return (1-1/r)/r**2
    low = brentq(lambda r:pot(r)-1/B**2,wall,1.5)
    high = brentq(lambda r:pot(r)-1/B**2,1.5,10.)
    integral = quad(lambda r:math.sqrt(max(0.,pot(r)-1/B**2))/(1-1/r),
                    low,high,epsabs=2e-12)[0]
    return dict(source_over_rs=source, wall_over_rs=wall, weights=rows,
                turning_points_for_B3=[low,high], barrier_action_per_angular_momentum=integral)


def main():
    timing = clocks()
    data = dict(boundary=susceptibility(), finite_matter=finite_matter(),
                angular_barrier=exterior(), timing=timing, late_window=late_window(), mobile_tip=mobile_tip(),
                tension_release=tension_release(timing["capture_episodes"][-1]),
                quantum_recoil=quantum_recoil(), terminal_decay=terminal_decay(),
                maxwell_exterior=maxwell_outlet())
    OUT.write_text(json.dumps(data, indent=2, allow_nan=False)+"\n", encoding="utf8")
    print(OUT.name)


if __name__ == "__main__":
    main()
