"""Causal domains, conditional sector weights, and a matter probe of one CAT interior.

The spacetime comparison uses an exact theorem, not a sampling of exotic smoothings.
The quantum calculation has one dynamical compact coordinate. Time and momenta
use the deep-branch units of volume 7, T.9. Run from the project or reproduction bundle.
"""
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq

import cat_relational_waves as waves

ROOT = Path(__file__).resolve().parents[1]


def vacuum_instrument():
    """A receiving device updates a material bit within one of two central blocks."""
    vacuum = np.diag([1., 1., 0., 0.])
    state = vacuum / 2
    bit = np.diag([1., 0., 1., 0.])
    rows = []
    for resolution in (0., .25, .5, .75, 1.):
        effect = (np.eye(4) + resolution * (2 * bit - np.eye(4))) / 2
        operator = np.diag(np.sqrt(np.diag(effect)))
        updated = operator @ state @ operator
        probability = np.trace(updated)
        updated /= probability
        other_sector = np.trace((np.eye(4) - vacuum) @ updated)
        bit_given_receipt = np.trace(bit @ updated)
        assert other_sector == 0 and abs(bit_given_receipt - (1 + resolution) / 2) < 1e-14
        rows.append(dict(resolution=resolution, outcome_probability=probability,
                         bit_given_outcome=bit_given_receipt, outside_sector=other_sector))
    return rows


def longitudinal_blocks():
    """Use fixed total rank, identifiable far-separated blocks and equal |p_perp|."""
    transfers = []
    for n, m, q in ((4, 4, 1), (3, 4, 1), (7, 5, -1)):
        before = Fraction(1, n) + Fraction(1, m)
        after = Fraction(1, n+q) + Fraction(1, m-q)
        expected = Fraction(q*(n-m+q), (n+q)*(m-q))
        assert after/before-1 == expected
        transfers.append(dict(initial=[n, m], final=[n+q, m-q], relative_energy_change=str(expected)))
    coherent = np.ones((2, 2))/2
    exchange = np.array([[0., 1.], [1., 0.]])
    charge_read = np.diag(np.diag(coherent))
    assert np.trace(coherent @ exchange) == 1. and np.trace(charge_read @ exchange) == 0.
    phases = []
    for n, m, speed, impact in ((3, 4, .2, 7.), (4, 3, .2, 7.), (2, 5, .3, 8.)):
        factor = n*m*speed**3/impact**6
        direct = quad(lambda x: (15/16)*factor/(1+x*x)**3.5, -np.inf, np.inf,
                      epsabs=1e-19, epsrel=1e-12)[0]
        assert abs(direct/factor-1) < 2e-13
        phases.append(dict(ranks=[n,m],speed=speed,impact=impact,phase=direct))
    membrane = []
    for distance in (2., 6.):
        zero = 3*np.pi/(8*distance**5)
        for quantum in (1, 2):
            s = distance*quantum  # Spacelike R11=1 in longitudinal rest units.
            integral = 2*quad(lambda y: (distance**2+y*y)**-3, 0., np.inf,
                              weight="cos",wvar=quantum,epsabs=2e-15)[0]
            predicted = np.exp(-s)*(1+s+s*s/3)
            assert abs(integral/zero-predicted) < 2e-11
            membrane.append(dict(r_over_R=distance, transfer=quantum, relative_kernel=integral/zero))
    return dict(transfers=transfers, elastic_phases=phases, membrane_target=membrane, reversible_visibility=1.,
                resolved_and_averaged_visibility=0.)


def cosmological_volume():
    """An exact homogeneous C1 preparation, two physical normal modes and relational endpoints."""
    def rhs(t, state):
        u = state[:2]
        return [*state[2:], *(-2*np.dot(u,u)*u)]

    initial = [1., 0., 0., .5]
    settings = dict(method="DOP853", rtol=4e-13, atol=2e-14, max_step=.018, dense_output=True)
    past = solve_ivp(rhs, (0., -.53), initial, **settings)
    future = solve_ivp(rhs, (0., .53), initial, **settings)
    assert past.success and future.success

    def geometry(t):
        return (future if t >= 0 else past).sol(t)

    endpoint = .5
    h = np.sqrt(8.)
    rows = []
    for family, rank in (("angular", None), ("longitudinal", 128), ("longitudinal", 256),
                         ("longitudinal", None)):
        def frequency_squared(t):
            if family == "angular":
                position = geometry(t)[:2]
                return 2*np.dot(position,position)
            if rank is None:
                velocity = geometry(t)[2:]
                return h*h*np.dot(velocity,velocity)
            casimir = np.sqrt(rank*(rank+1))
            separation = h/(2*casimir)
            difference = geometry(t+separation)[:2] - geometry(t-separation)[:2]
            return casimir**2*np.dot(difference,difference)

        omega = np.sqrt(frequency_squared(-endpoint))
        end_omega = np.sqrt(frequency_squared(endpoint))
        np.testing.assert_allclose(omega, end_omega, atol=3e-13)
        z0 = 1/np.sqrt(2*omega)
        matter = solve_ivp(lambda t,y: [y[1], -frequency_squared(t)*y[0]],
                           (-endpoint, endpoint), [z0+0j, -1j*omega*z0], **settings)
        assert matter.success
        z, velocity = matter.y[:, -1]
        occupation = (abs(velocity)**2 + abs(end_omega*z)**2)/(2*end_omega)-.5
        wronskian = -2*np.imag(np.conj(z)*velocity)
        assert abs(wronskian-1) < 2e-12 and occupation > 0
        rows.append(dict(family=family,spin=rank, endpoint_frequency=omega, mean_occupation=occupation,
                         excited_probability=1-1/np.sqrt(1+occupation),wronskian=wronskian))
    assert abs(rows[2]["mean_occupation"]-rows[3]["mean_occupation"]) < 6e-5
    z = geometry(endpoint)
    a2 = z[:2]@z[:2]
    age = quad(lambda t: np.linalg.norm(geometry(t)[:2])*np.linalg.norm(geometry(t)[2:])**.5,
               0., endpoint, epsabs=1e-13)[0]
    return dict(angular_momentum=.5, energy=1.25, lower_volume_per_solid_angle=.5/1.25**.25,
                turn_volume_per_solid_angle=1/np.sqrt(2.), radial_null_ricci=-28.,
                proper_volume_acceleration=10.5, endpoint_a_squared=a2, proper_half_duration=age,
                endpoint_trace_angle=np.arctan2(z[1], z[0]), matter=rows)


def spherical_contacts():
    """Off-diagonal Yukawa operator between the moving sphere and a test D0 block."""
    identity = np.eye(2)
    sx, sy, sz = waves.SIGMA
    gammas = []
    for k in range(3):
        for active in (sx, sy):
            gamma = np.ones((1, 1))
            for factor in [sz]*k+[active]+[identity]*(3-k):
                gamma = np.kron(gamma, factor)
            gammas.append(gamma)
    rows = []
    for j in (.5, 1., 2.):
        m = np.arange(-j, j+1)
        raising = np.diag(np.sqrt((j-m[:-1])*(j+m[:-1]+1)), -1)
        spin = [(raising+raising.T)/2, (raising-raising.T)/(2.0j), np.diag(m)]
        first = sum(np.kron(gammas[i],spin[i]) for i in range(3))
        second = sum(np.kron(gammas[i+3],spin[i]) for i in range(3))
        offset = np.kron(gammas[2],np.eye(len(m)))
        values, vectors = np.linalg.eigh(first-j*offset)
        kernel = vectors[:, abs(values)<1e-10]
        slopes = np.linalg.eigvalsh(kernel.conj().T @ (.5*second) @ kernel)
        center_gap = min(abs(np.linalg.eigvalsh(first)))
        assert len(slopes)==8 and abs(center_gap-j)<2e-13
        np.testing.assert_allclose(slopes, [-j/2]*4+[j/2]*4, atol=2e-13)
        rows.append(dict(spin=j,central_gap=center_gap,contact_nullity=len(slopes),
                         negative_slopes=int(sum(slopes<0)), positive_slopes=int(sum(slopes>0)),
                         min_slope=slopes[0], max_slope=slopes[-1]))
    return rows


def compact_protocol():
    """Invert finite past-cone charts and independently integrate the two-mode Gaussian tail."""
    endpoint = np.array([2., -.5, 1.])
    greatest_error = 0.
    for separation in ((0., 0., 0.), (.4, -1.7, .25), (-3., .1, 1.)):
        for depth in (.25, 1., 3.5):
            start = endpoint + separation
            time_separation = np.sqrt(np.dot(separation, separation) + depth ** 2)
            recovered = np.sqrt(time_separation ** 2 - np.dot(start - endpoint, start - endpoint))
            greatest_error = max(greatest_error, abs(depth - recovered))
    assert greatest_error < 1e-13
    tails = []
    for buffer in (1., 2., 3., 4.):
        direct = quad(lambda r: 2*r**3*np.exp(-r*r), buffer, np.inf, epsabs=1e-15)[0]
        bound = (1+buffer**2)*np.exp(-buffer**2)
        np.testing.assert_allclose(direct, bound, rtol=2e-13)
        tails.append(dict(buffer=buffer, direct=direct, bound=bound))
    return dict(cone_chart_max_error=greatest_error, coherent_buffer=tails,
                exterior_smooth_types="DeMichelis-Freedman; no exotic space is discretized in this check")


def two_wave_profile(u, turn_on):
    # Complex-step differentiation stays on the smooth germ at each sampled real u.
    root = np.sqrt(1+u*u)
    angle = turn_on*np.exp(1-1/u) if u.real > 0 else 0.
    rate = angle/u**2 if u.real > 0 else 0.
    axis = np.array([np.cos(angle), np.sin(angle)])
    transverse = np.array([-axis[1], axis[0]])
    pair = root*axis
    pair_derivative = u/root*axis + root*rate*transverse
    return u, 1., waves.spin_tensor(pair), waves.spin_tensor(pair_derivative)


def screen_profile(u, strength):
    f, _, matrix, slope = two_wave_profile(u, strength)
    s = 1+f*f
    derivative = slope[0]/s**2 - 2*f*matrix[0]/s**3
    return -waves.rotation(f*f) @ ((s*np.eye(2)+waves.J) @ derivative)


def common_wave():
    """Realize the minimax comparison tide by the inverse matrix equations of volume 4."""
    def target(t):
        u = 2*np.sinh(np.arcsinh(1.5*t)/3)
        return (screen_profile(u, 0.) + screen_profile(u, 1.))/2

    def rhs(t, state):
        f, mx, my, _ = state
        s = 1+f*f
        dm = -np.linalg.solve(s*np.eye(2)+waves.J, waves.rotation(-f*f) @ target(t))
        return [np.hypot(mx, my)/np.sqrt(s), *dm, 1/s]

    start, end = -.5 - .5**3/3, 1+1/3
    # Start on the same pre-separation matrix wave in this numerical example.
    evolution = solve_ivp(rhs, (start, end), [-.5, 1/np.sqrt(1.25), 0., -.5],
                          method="DOP853", rtol=3e-12, atol=3e-14, max_step=.018, dense_output=True)
    assert evolution.success
    delta = 1e-4
    residual, min_amplitude = 0., np.inf
    for t in np.linspace(start+2*delta, end-2*delta, 181):
        f, mx, my, _ = evolution.sol(t)
        min_amplitude = min(min_amplitude, np.hypot(mx, my))
        dm = (evolution.sol(t+delta)[1:3]-evolution.sol(t-delta)[1:3])/(2*delta)
        reconstructed = -waves.rotation(f*f) @ (((1+f*f)*np.eye(2)+waves.J) @ dm)
        residual = max(residual, np.linalg.norm(reconstructed-target(t)))
    tensor_error = np.linalg.norm(screen_profile(1., 1.)-screen_profile(1., 0.))/2
    assert residual < 3e-6 and min_amplitude > .05
    return dict(equal_tolerance_full_screen=tensor_error, reconstruction_max_error=residual,
                minimum_sampled_amplitude=min_amplitude, interval=[start, end])


def curved_extensions():
    rows = []
    # Test the curvature in the original Darboux variables, without using a
    # Brinkmann trace formula to compute the numerical Ricci or tidal eigenvalues.
    with patch.object(waves, "profile", two_wave_profile):
        for u in (-.5, .5, 1.):
            for strength in (0., 1.):
                s = 1+u*u
                rate = strength*np.exp(1-1/u)/u**2 if u > 0 else 0.
                theory = np.sqrt((s*s+1)*(u*u/s**5 + rate**2/s**3))
                location = np.array([u, .2, 0., 0.])
                ricci, curvature = waves.direct_curvature(location, strength, .002)
                # Along x=0, dt=s du; the orthonormal screen is rotated relative
                # to y,z, leaving its eigenvalues unchanged.
                tidal = np.linalg.eigvalsh(curvature[0,2:,0,2:]/s**2)
                np.testing.assert_allclose(tidal, [-theory, theory], atol=1.5e-7)
                assert abs(ricci).max() < 5e-7
                rows.append(dict(u=u, strength=strength, signed_eigenvalues=tidal.tolist(),
                                 analytic_amplitude=theory, ricci_max=abs(ricci).max()))
    a, b = (row["analytic_amplitude"] for row in rows[-2:])
    assert abs(b/a-np.sqrt(5)) < 1e-14
    # Exact Weyl shifts on exp(i v), y=1,z=0, in the unrotated profile.
    with localcontext() as ctx:
        ctx.prec = 50
        one = Decimal(1)
        phi = lambda u: (one+u*u).sqrt()/2
        first = one/(2*Decimal(2).sqrt())
        coefficient = one/(32*Decimal(2).sqrt())  # -Phi'''(1)/12
        ratios = []
        for stepsize in ("0.02", "0.01", "0.005"):
            h = Decimal(stepsize)
            correction = (-2*(phi(one+h/2)-phi(one-h/2))/h+2*first)/h**2
            ratios.append(float(correction/coefficient))
        assert max(abs(r-1) for r in ratios) < 2e-5
    return dict(curvature=rows, equal_tolerance_minimum=(b-a)/2, comparison_wave=common_wave(),
                weyl_shift_ratios=ratios, quartic_probe_correction_per_hbar_squared=24*float(coefficient))


def quantum_response(points, steps, epsilon=.2, share=.2):
    center = np.sqrt(2 * (1 - 2 * share) / 3) / share
    initial_momentum = share * center**3
    gamma = share / initial_momentum**2
    spread = np.sqrt(epsilon / (2 * np.sqrt(6) * center))
    width = 8.
    position = np.arange(points) * (2 * width / points) - width
    momentum = 2 * np.pi * epsilon * np.fft.fftfreq(points, 2 * width / points)
    state = np.exp(-(position - center)**2 / (4 * spread**2) + 1j * initial_momentum * position / epsilon)
    state /= np.linalg.norm(state)
    times = np.linspace(0., .16, steps + 1)
    dt = times[1]
    potential_step = np.exp(-.25j * dt * position**4 / epsilon)
    kinetic_step = np.exp(-.5j * dt * momentum**2 / epsilon)
    # Each column is derived independently from the instantaneous wave function.
    values = np.empty((steps + 1, 5))
    max_edge_probability = 0.
    for index in range(steps + 1):
        fourier = np.fft.fft(state, norm="ortho")
        momentum_state = np.fft.ifft(momentum * fourier, norm="ortho")
        probability = abs(state)**2
        kinetic = np.vdot(momentum_state, momentum_state).real
        current = np.vdot(position**3 * state, momentum_state).real
        force_squared = 8 * (probability @ position**6)
        mixed = 12 * (abs(momentum_state)**2 @ position**2)
        values[index] = (1 - share + gamma * kinetic, -4 * gamma * current,
                         gamma * force_squared, gamma * mixed, (kinetic + probability @ position**4) / 2)
        max_edge_probability = max(max_edge_probability, np.sum(probability[abs(position) > 7.]),
                                   np.sum(abs(fourier[abs(momentum) > .85 * max(abs(momentum))])**2))
        if index < steps:
            state = potential_step * np.fft.ifft(kinetic_step * np.fft.fft(potential_step * state))
    interpolated = CubicSpline(times, values, axis=0)
    turn = brentq(lambda t: interpolated(t)[1], 0., times[-1])
    index = int(round(turn / dt))
    q_values = values[:, 0]
    # Five-point derivatives do not use the commutator or the force equation.
    window = q_values[index - 2:index + 3]
    fd_velocity = window @ np.array([1, -8, 0, 8, -1]) / (12 * dt)
    fd_acceleration = window @ np.array([-1, 16, -30, 16, -1]) / (12 * dt**2)
    ordering = 6 * gamma * epsilon**2
    force_index = values[index, 2] - values[index, 3] + ordering
    q_turn, _, positive, subtracted, _ = interpolated(turn)
    acceleration = positive - subtracted + ordering
    angular = (1 - turn / 2)**2 + (turn / 2)**2
    null_moment_metric = -acceleration / (2 * angular * q_turn**1.5)
    drift = np.max(abs(values[:, 4] / values[0, 4] - 1))
    assert 0 < turn < .16 and null_moment_metric < 0
    assert abs(fd_velocity - values[index, 1]) < 3e-6
    assert abs(fd_acceleration / force_index - 1) < 4e-6
    assert max_edge_probability < 1e-12 and drift < 2e-6
    return dict(points=points, steps=steps, epsilon=epsilon, share=share,
                turn=turn, q_initial=q_values[0], q_turn=q_turn, angular_at_turn=angular,
                quartic_force_term=positive, mixed_term=subtracted, ordering_term=ordering,
                second_derivative_at_turn=acceleration, radial_null_moment_metric=null_moment_metric,
                finite_difference_acceleration=fd_acceleration, operator_acceleration_same_step=force_index,
                finite_difference_velocity=fd_velocity, operator_velocity_same_step=values[index, 1],
                energy_drift=drift, edge_probability=max_edge_probability)


def run():
    coarse = quantum_response(1024, 480)
    fine = quantum_response(2048, 960)
    for key in ("turn", "q_turn", "second_derivative_at_turn", "radial_null_moment_metric"):
        np.testing.assert_allclose(coarse[key], fine[key], rtol=2e-6, atol=1e-8)
    return dict(causal_chart=compact_protocol(), curved_extensions=curved_extensions(),
                fixed_vacuum=vacuum_instrument(), longitudinal_blocks=longitudinal_blocks(),
                homogeneous_volume=cosmological_volume(), material_contacts=spherical_contacts(),
                reduced_quantum_response=dict(coarse=coarse, fine=fine))


if __name__ == "__main__":
    output = ROOT / "verification/cat-observer-domains-results.json"
    output.write_bytes((json.dumps(run(), indent=2, allow_nan=False) + "\n").encode("utf8"))
