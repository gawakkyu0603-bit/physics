"""Evolve the direct scalar contact in four-dimensional homogeneous gravity.

Each occupied layer has its own proper time, metric, scalar and positive-energy
clock/rods. Radiation follows its own metric. Equal clock readings specify the
contact. All numerical scales are preparations or couplings for a comparison.
"""
import math

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import solve_banded

from layer_contact_geometry import causal_source_checks, circle_coupling_checks, compact_collapse_data


class LayerGravity:
    def __init__(self, fraction, xi=.25, contact=.8, sign=1, amplitude=.75):
        self.fraction = fraction
        self.weights = np.array([1-fraction, fraction])
        self.xi, self.contact, self.sign = xi, contact, sign
        self.amplitude = amplitude
        self.mass2, self.quartic = .04, .18
        self.radiation0, self.rod = .90, .10
        self.clock0 = .50
        self.initial_fields = np.array([0., amplitude])

    def terms(self, scale, field, velocity, clock):
        w = self.weights
        f = 1+self.xi*field**2
        fp = 2*self.xi*field
        density = self.radiation0/scale**4
        rods = (self.rod/scale)**2
        single = self.mass2*field**2/2+self.quartic*field**4/4
        single_prime = self.mass2*field+self.quartic*field**3
        squares = field**2
        mean_square = w @ squares
        potential = self.contact*(w @ ((squares-mean_square)**2))/2
        source = 2*self.contact*field*(squares-mean_square)
        energy = density+(velocity**2+clock**2+3*rods)/2+single+potential
        return f, fp, density, rods, single_prime, potential, source, energy

    def constraint_hubble(self, scale, field, velocity, clock):
        f, fp, *_, energy = self.terms(scale, field, velocity, clock)
        fdot = fp*velocity
        return (-3*fdot+self.sign*np.sqrt(9*fdot**2+12*f*energy))/(6*f)

    def rates(self, scale, field, velocity, clock, hubble):
        f, fp, radiation, rods, single_prime, potential, source, energy = self.terms(
            scale, field, velocity, clock)
        volume = scale**3/clock
        volume_ratio = (self.weights @ volume)/volume
        potential_reading_rate = self.weights @ (source*velocity/clock)
        clock_accel = -3*hubble*clock-potential_reading_rate+volume_ratio*source*velocity/clock
        bare_accel = -3*hubble*velocity-single_prime-volume_ratio*source+6*fp*hubble**2
        enthalpy = 4*radiation/3+velocity**2+clock**2+rods
        hdot = (-enthalpy-2*self.xi*velocity**2-fp*bare_accel+hubble*fp*velocity)/(2*f+3*fp**2)
        field_accel = bare_accel+3*fp*hdot
        balances = 3*f*hubble**2+3*hubble*fp*velocity-energy
        return hdot, field_accel, clock_accel, balances, potential

    def solve(self, duration, constrained=False):
        start_scale = np.ones(2)
        start_clock = np.full(2, self.clock0)
        start_velocity = np.zeros(2)
        initial_h = self.constraint_hubble(start_scale, self.initial_fields, start_velocity, start_clock)
        initial = np.r_[start_scale, self.initial_fields, start_velocity,
                        ([start_clock[0]] if constrained else np.r_[start_clock, initial_h]),
                        0., 0.]
        clock_charge = self.weights @ (start_scale**3*start_clock)

        def unpack(state):
            scale, field, velocity = state[:2], state[2:4], state[4:6]
            if constrained:
                cq = state[6]
                cs = (clock_charge-self.weights[0]*scale[0]**3*cq)/(self.weights[1]*scale[1]**3)
                clock = np.array([cq, cs])
                hubble = self.constraint_hubble(scale, field, velocity, clock)
            else:
                clock, hubble = state[6:8], state[8:10]
            return scale, field, velocity, clock, hubble

        def rhs(_, state):
            scale, field, velocity, clock, hubble = unpack(state)
            hdot, acceleration, clock_accel, _, _ = self.rates(scale, field, velocity, clock, hubble)
            time_ratio = clock[0]/clock  # d tau_i / d tau_quiet at equal clock readings
            shared = np.r_[scale*hubble*time_ratio, velocity*time_ratio, acceleration*time_ratio]
            auxiliary = ([clock_accel[0]] if constrained else np.r_[clock_accel*time_ratio, hdot*time_ratio])
            return np.r_[shared, auxiliary, clock[0], time_ratio[1]]

        sol = solve_ivp(rhs, (0., duration), initial, method="DOP853", rtol=5e-13,
                        atol=1e-15, dense_output=True)
        assert sol.success

        def observe(time):
            state = sol.sol(time)
            scale, field, velocity, clock, hubble = unpack(state)
            assert min(scale) > 0 and min(clock) > 0
            hdot, _, _, balance, potential = self.rates(scale, field, velocity, clock, hubble)
            ricci = 6*(hdot[0]+2*hubble[0]**2)
            trace_ricci = 4*potential-clock[0]**2+3*(self.rod/scale[0])**2
            assert abs(ricci-trace_ricci) < 2e-10
            charge_error = self.weights @ (scale**3*clock)-clock_charge
            return dict(ricci=float(ricci), tide=float(hdot[0]+hubble[0]**2),
                        quiet_h=float(hubble[0]), active_proper_time=float(state[-1]),
                        reading=float(state[-2]), active_field=float(field[1]),
                        constraint_error=float(max(abs(balance))), clock_error=float(abs(charge_error)))
        return observe

    def initial_curvature_difference(self):
        p, s = self.fraction, self.amplitude
        f, fp = 1+self.xi*s*s, 2*self.xi*s
        screening = 2*f/(2*f+3*fp*fp)
        return -24*screening*self.contact**2*p*(1-p)*(1-2*p)*s**6


def compare_complements(fraction, xi=.25, contact=.8, sign=1):
    duration = .32 if sign > 0 else .20
    cases = [LayerGravity(p, xi, contact, sign) for p in (fraction, 1-fraction)]
    full = [case.solve(duration) for case in cases]
    constrained = [case.solve(duration, constrained=True) for case in cases]
    largest_reduction_error = largest_constraint = largest_charge = 0.
    for time in np.linspace(0, duration, 17):
        for evolved, projected in zip(full, constrained):
            a, b = evolved(time), projected(time)
            largest_reduction_error = max(largest_reduction_error,
                *(abs(a[name]-b[name]) for name in ("ricci", "tide", "active_field", "active_proper_time", "reading")))
            largest_constraint = max(largest_constraint, a["constraint_error"])
            largest_charge = max(largest_charge, a["clock_error"])
    assert max(largest_reduction_error, largest_constraint, largest_charge) < 2e-10
    step = .0025
    times = np.arange(1, 7)*step
    scaled = np.array([(full[0](t)["ricci"]-full[1](t)["ricci"])/t**2 for t in times])
    curvature_second = 2*np.polynomial.polynomial.polyfit(times/step, scaled, 4)[0]
    expected = cases[0].initial_curvature_difference()
    assert abs(curvature_second-expected) < 4e-8
    final = [f(duration) for f in full]
    return (dict(active_fraction=fraction, jordan_coupling=xi, contact_coupling=contact,
                 expansion_sign=sign, predicted_curvature_second=expected,
                 fitted_curvature_second=float(curvature_second), quiet_proper_time=duration,
                 final_ricci_difference=final[0]["ricci"]-final[1]["ricci"],
                 final_hubble_difference=final[0]["quiet_h"]-final[1]["quiet_h"],
                 final_active_proper_times=[data["active_proper_time"] for data in final],
                 largest_constraint_residual=largest_constraint, largest_charge_residual=largest_charge,
                 largest_independent_reduction_error=largest_reduction_error), full)


def hydrogen_receiver(geometries, curvature_second):
    # Radial hydrogen, l=0, in atomic units. Common evolution is included for both histories.
    moment = lambda n: quad(lambda r: 4*r**(n+2)*math.exp(-2*r), 0, np.inf, epsabs=1e-12)[0]
    variance = moment(4)-moment(2)**2
    two_s = quad(lambda r: r**4*(2-r)*math.exp(-1.5*r)/math.sqrt(2), 0, np.inf)[0]
    assert abs(variance-13.5) < 2e-12 and abs(two_s+512*math.sqrt(2)/243) < 2e-13
    ratio = .20  # units of inverse geometry time per unit atomic time
    predicted = (ratio**4*curvature_second)**2/384
    def propagation(duration, spacing):
        radius = np.arange(spacing, 24., spacing)
        wave = (2*radius*np.exp(-radius)).astype(complex)
        wave /= np.linalg.norm(wave)
        delta_wave = np.zeros_like(wave)
        steps, off_diagonal = 100, -.5/spacing**2
        dt = duration/steps
        for step in range(steps):
            t = ratio*(step+.5)*dt
            tides = [ratio**2*source(t)["tide"] for source in geometries]
            diagonals = [1/spacing**2-1/radius-tide*radius**2/2 for tide in tides]
            def advance(state, diagonal, forcing=None):
                rhs = (1-.5j*dt*diagonal)*state
                rhs[1:] -= .5j*dt*off_diagonal*state[:-1]
                rhs[:-1] -= .5j*dt*off_diagonal*state[1:]
                if forcing is not None:
                    rhs += forcing
                band = np.zeros((3, len(state)), dtype=complex)
                band[1] = 1+.5j*dt*diagonal
                band[2, :-1] = band[0, 1:] = .5j*dt*off_diagonal
                return solve_banded((1, 1), band, rhs)
            after = advance(wave, diagonals[1])
            # Exact discrete difference of the two implicit midpoint equations.
            delta_h = -(tides[0]-tides[1])*radius**2/2
            delta_wave = advance(delta_wave, diagonals[0], -.5j*dt*delta_h*(wave+after))
            wave = after
        perpendicular = delta_wave-np.vdot(wave, delta_wave)*wave
        assert abs(np.vdot(wave, wave).real-1) < 5e-13
        return float(np.vdot(perpendicular, perpendicular).real/duration**6)
    times = [.08, .04, .02]
    rows = []
    for spacing in (.08, .04):
        coefficients = [propagation(t, spacing) for t in times]
        extrapolated = (coefficients[0]-6*coefficients[1]+8*coefficients[2])/3
        assert abs(extrapolated/predicted-1) < .001
        rows.append(dict(radial_spacing=spacing, times=times, scaled_coefficients=coefficients,
                         extrapolated=extrapolated, relative_error=abs(extrapolated/predicted-1)))
    return dict(atomic_time_ratio=ratio, exact_complete_variance=variance,
                matrix_element_2s=two_s, tangent_fraction_2s=two_s**2/variance,
                predicted_short_time_coefficient=predicted, radial_solves=rows)


def receiver_width_check():
    # Read the two pure hypotheses on the minimum-error axis for each captured block.
    # Failures are flagged erasures. Test the closed expression by direct measurement.
    overlap, efficiency, copies = .82, .61, 4
    expected_var = 0.
    for received in range(copies+1):
        prob = math.comb(copies, received)*efficiency**received*(1-efficiency)**(copies-received)
        f = overlap**received
        state_a = np.array([math.sqrt((1+f)/2), math.sqrt((1-f)/2)])
        state_b = np.array([state_a[0], -state_a[1]])
        measurement = np.array([[1., 1.], [1., -1.]])/math.sqrt(2)
        pa, pb = (measurement @ state_a)**2, (measurement @ state_b)**2
        posterior = pa/(pa+pb)
        expected_var += prob*sum((pa+pb)/2*posterior*(1-posterior))
    formula = (1-efficiency+efficiency*overlap**2)**copies/4
    assert abs(expected_var-formula) < 1e-14
    return dict(overlap=overlap, copies=copies, flagged_capture=efficiency,
                measured_indicator_variance=expected_var, formula=formula, exterior_variance=.25)


def live_layer_checks():
    baseline, fields = compare_complements(1/3)
    quarter, _ = compare_complements(1/4)
    collapsing, contracting_fields = compare_complements(1/3, sign=-1)
    minimal, _ = compare_complements(1/3, xi=0.)
    control, _ = compare_complements(1/3, contact=0.)
    ratio = baseline["fitted_curvature_second"]/quarter["fitted_curvature_second"]
    assert abs(ratio-64/81) < 3e-7 and abs(control["final_ricci_difference"]) < 1e-10
    collapse = [compact_collapse_data(LayerGravity(p, sign=-1)) for p in (1/3, 2/3)]
    for a, b in zip(collapse[0]['sectors'], collapse[1]['sectors']):
        assert abs(a['schwarzschild_radius_parameter']-b['schwarzschild_radius_parameter']) < 3e-12
    evolution_curves = []
    for record, models in [(baseline, fields), (collapsing, contracting_fields)]:
        times = np.linspace(0., record['quiet_proper_time'], 45)
        leading = record['predicted_curvature_second']/2
        values = [leading]+[(models[0](t)['ricci']-models[1](t)['ricci'])/t**2 for t in times[1:]]
        evolution_curves.append(dict(proper_times=times.tolist(), scaled_curvature=values))
    return dict(complementary_preparations=[baseline, quarter, collapsing, minimal, control],
                evolution_curves=evolution_curves,
                compact_collapsing_data=collapse, circle_quartics=circle_coupling_checks(),
                causal_circle_source=causal_source_checks(), received_width=receiver_width_check(),
                identical_coupling_ratio=ratio,
                hydrogen=hydrogen_receiver(fields, baseline["predicted_curvature_second"]))
