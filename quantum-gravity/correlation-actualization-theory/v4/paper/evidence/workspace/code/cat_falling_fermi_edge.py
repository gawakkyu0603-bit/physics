"""A Yukawa crossing of two falling matrix blocks in homogeneous dust.

Lengths in the eigenvalue problem are matrix coordinates in units of 1/u_i.
Time is elapsed proper time divided by the initial time to dust focusing u_i.
The fermionic computation uses classical bosonic matrices, quantum quadratic
probe--block fermions and a prescribed ordinary tidal field.
"""
import json
from math import comb
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import null_space
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
SIGMA = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
T_END = 7 / 8
T_HORIZON = 26 / 27
DRIFT = 33 / 128
DUST_TO_HORIZON = 27
SOLAR_GRAVITY_TIME_S = 4.92549095e-6


def tide(t, dust):
    return 2 / (9 * (1 - t)**2) if dust else 0.


def fundamental(t):
    s = np.cbrt(1 - t)
    return 2 * s - s**2, 3 * s * (1 - s)


def radial_trial(j, drift, dust, end=T_END):
    """The ordinary self-contracting sphere, compared with a freely moving point."""
    def equation(t, state):
        radius, radial_speed, point, point_speed = state
        curvature = tide(t, dust)
        return [radial_speed, -curvature * radius - 2 * radius**3 / j**2,
                point_speed, -curvature * point]

    def crossing(t, state):
        return state[0] - state[2]

    solution = solve_ivp(equation, (0, end), [1., 0., 1.25, -drift],
                         events=crossing, dense_output=True, method="DOP853",
                         rtol=2e-12, atol=2e-14, max_step=.04)
    assert solution.success
    sample_times = np.linspace(0, end, 101)
    radius, _, point, _ = solution.sol(sample_times)
    free_radius, free_speed_response = (fundamental(sample_times) if dust
                                        else (np.ones_like(sample_times), sample_times))
    np.testing.assert_allclose(point, 1.25 * free_radius - drift * free_speed_response, atol=1e-11)
    assert np.all(radius <= free_radius + 1e-11)
    assert np.all(radius >= free_radius - sample_times**2 / j**2 - 1e-11)
    roots = solution.t_events[0]
    event = {}
    if len(roots):
        assert len(roots) == 1
        crossing_time = float(roots[0])
        time_left_in_horizon_units = DUST_TO_HORIZON * (1 - crossing_time)
        event = dict(crossing_elapsed=crossing_time,
                     boundary_radius_over_schwarzschild=time_left_in_horizon_units**(2/3),
                     proper_margin_microseconds_10_solar=(time_left_in_horizon_units - 1)
                     * 4/3 * 10 * SOLAR_GRAVITY_TIME_S * 1e6,
                     conformal_range=2 * (np.cbrt(time_left_in_horizon_units) - 1))
    return dict(spin=j, speed=drift, dust=dust, end=end, final_gap=float(radius[-1]-point[-1]), **event)


def spin_matrices(j):
    magnetic_number = np.arange(j, -j-1, -1)
    raising = np.diag(np.sqrt((j - magnetic_number[1:]) * (j + magnetic_number[1:] + 1)), 1)
    return np.array([(raising+raising.T)/2, (raising-raising.T)/2.0j, np.diag(magnetic_number)])


def commutator(left, right):
    return left @ right - right @ left


def localizer(positions, probe_z):
    size = positions.shape[1]
    displacement = positions.copy()
    displacement[2] -= probe_z * np.eye(size)
    return sum(np.kron(spin, coord) for spin, coord in zip(SIGMA, displacement))


def fermion_force(delta, size):
    blocks = delta.reshape(2, size, 2, size)
    return np.einsum("iab,brac->irc", SIGMA, blocks)


def mixed_trial(j, strength, dust, refine=False, end=T_END):
    """Keep every matrix entry of the three-plane and both probe chiralities.

    All four copies in each chirality start alike. The factor four accounts
    for them in energy, force and Gauss' law. Gauge fixing sets A_t = 0.
    """
    n = 2*j + 1
    matrix_entries = 3*n*n
    covariance_entries = 4*n*n
    eye = np.eye(n)
    body = spin_matrices(j) / j
    body[2] -= (1.25/(n+1)) * eye
    probe = n*1.25/(n+1)
    body_velocity = np.zeros_like(body)
    body_velocity[2] = DRIFT/(n+1) * eye
    probe_velocity = -n*DRIFT/(n+1)
    values, vectors = np.linalg.eigh(localizer(body, probe))
    occupied = vectors[:, values < 0]
    plus = occupied @ occupied.conj().T
    minus = np.eye(2*n) - plus

    def pack(position, speed, cplus, cminus, point, velocity, work):
        return np.concatenate([position.ravel(), speed.ravel(), cplus.ravel(),
                               cminus.ravel(), [point, velocity, work]])

    def unpack(state):
        pos_stop = matrix_entries
        vel_stop = 2 * pos_stop
        plus_stop = vel_stop + covariance_entries
        return (state[:pos_stop].reshape(3, n, n), state[pos_stop:vel_stop].reshape(3, n, n),
                state[vel_stop:plus_stop].reshape(2*n, 2*n),
                state[plus_stop:-3].reshape(2*n, 2*n), *state[-3:])

    def energy(state, t):
        pos, vel, cp, cm, y, vy, _ = unpack(state)
        kinetic = .5 * (np.sum(np.abs(vel)**2) + abs(vy)**2)
        quartic = .5 * sum(np.sum(np.abs(commutator(pos[i], pos[k]))**2)
                           for i in range(3) for k in range(i))
        trap = .5 * tide(t, dust) * (np.sum(np.abs(pos)**2) + abs(y)**2)
        fermions = 4 * strength * np.trace((cp-cm) @ localizer(pos, y)).real
        return float(kinetic + quartic + trap + fermions)

    def derivatives(t, state):
        pos, vel, cp, cm, y, vy, _ = unpack(state)
        ham = localizer(pos, y)
        forces = fermion_force(cp-cm, n)
        acc = -tide(t, dust)*pos - 4*strength*forces
        for i in range(3):
            for k in range(3):
                if k != i:
                    acc[i] -= commutator(pos[k], commutator(pos[k], pos[i]))
        ay = -tide(t, dust)*y + 4*strength*np.trace(forces[2])
        work = ((2/(9*(1-t)**3)) * (np.sum(np.abs(pos)**2) + abs(y)**2)
                if dust else 0.)
        return pack(vel, acc, -1j*commutator(ham, cp), 1j*commutator(ham, cm), vy, ay, work)

    def crossing(t, state):
        pos, _, _, _, y, _, _ = unpack(state)
        return float((pos[2, 0, 0] - y).real)

    initial = pack(body, body_velocity, plus, minus, probe, probe_velocity, 0.)
    result = solve_ivp(derivatives, (0, end), initial, method="DOP853",
                       max_step=.02 if refine else .05, events=crossing,
                       rtol=8e-12 if refine else 3e-10, atol=1e-13 if refine else 3e-12)
    assert result.success
    final = result.y[:, -1]
    pos, vel, cp, cm, y, _, work = unpack(final)
    ham = localizer(pos, y)
    evals = np.linalg.eigvalsh(ham)
    boson_gauss = 1j * sum(commutator(x, dx) for x, dx in zip(pos, vel))
    matter_charge = np.trace((cp+cm-np.eye(2*n)).reshape(2,n,2,n), axis1=0, axis2=2)
    gauss = np.linalg.norm(boson_gauss - 4*strength*matter_charge)
    balance = abs((energy(final, end) - energy(initial, 0)) - work)
    assert gauss < 1e-8 and balance < 2e-8 * max(1., abs(work))
    assert np.linalg.norm(cp@cp-cp) < 2e-8 and np.linalg.norm(cm@cm-cm) < 2e-8
    assert abs(cp[0,0]-1) < 1e-9 and abs(cm[0,0]) < 1e-9
    assert np.linalg.norm(ham[1:,0]) < 1e-9
    # The protected state is the first basis vector. Check signs of the
    # complementary spectrum at every accepted step, even when no event fires.
    initial_negative_others = int(np.count_nonzero(np.linalg.eigvalsh(localizer(body,probe)[1:,1:]) < 0))
    other_gap = np.inf
    for step in result.y.T:
        step_pos, _, _, _, step_probe, _, _ = unpack(step)
        complementary = np.linalg.eigvalsh(localizer(step_pos,step_probe)[1:,1:])
        assert np.count_nonzero(complementary < 0) == initial_negative_others
        other_gap = min(other_gap, np.min(np.abs(complementary)))
    roots = result.t_events[0]
    gap = float((pos[2,0,0]-y).real)
    outside_index = int(np.sign(values).sum()/2)
    inside_index = int(np.sign(evals).sum()/2)
    assert outside_index == 0 and inside_index == int(gap > 0)
    centred = pos.copy()
    for i in range(3):
        centred[i] -= (np.trace(pos[i]) / n) * eye
    spread = [float(np.linalg.norm(x)) for x in centred]
    route = {}
    if len(roots) and dust:
        left = DUST_TO_HORIZON * (1 - roots[0])
        light_range = 2*(np.cbrt(left)-1)
        route = dict(boundary_radius_over_schwarzschild=float(left**(2/3)),
                     proper_margin_microseconds_10_solar=float((left-1)*4/3*10*SOLAR_GRAVITY_TIME_S*1e6),
                     conformal_range=float(light_range),
                     minimum_emitter_radius_over_surface=float(max(0.,1-light_range)))
    return dict(spin=j, dust=dust, strength=strength, end=end, crossings=len(roots), **route,
                crossing_elapsed=float(roots[0]) if len(roots) else None,
                final_index=inside_index, final_gap=gap, protected_pairs=4 if gap>0 else 0,
                protected_excess=8*max(gap,0.), final_norm_ratio=spread[2]/spread[0],
                other_gap_at_steps=float(other_gap), energy_balance_passed=True, gauss_check_passed=True)


def bosonic_fluctuations(j):
    """Check the extremal bosonic mode against the full transverse Hessian."""
    def frequency2(t, radius, point):
        return (point-radius)**2 - radius**2/j + tide(t, True)

    omega_i = np.sqrt(frequency2(0., 1., 1.25))
    width = 1/np.sqrt(2*omega_i)
    def evolve(t, state):
        radius, vr, point, vp, h, dh = state
        k = tide(t, True)
        return [vr, -k*radius - 2*radius**3/j**2, vp, -k*point,
                dh, -frequency2(t, radius, point)*h]

    def crossing(t, state):
        return (state[0]-state[2]).real

    result = solve_ivp(evolve, (0, T_END), [1., 0., 1.25, -DRIFT, width, -1j*omega_i*width],
                       method="DOP853", events=crossing, dense_output=True,
                       rtol=1e-11, atol=2e-13, max_step=.04)
    assert result.success
    t_hit = float(result.t_events[0][0])
    generators = spin_matrices(j)
    n = 2*j+1
    checks = []
    for t in (0., t_hit, T_END):
        radius, _, point, _, h, dh = result.sol(t)
        radius, point = radius.real, point.real
        coords = generators * (radius/j)
        coords[2] -= point*np.eye(n)
        divergence = np.hstack(coords)
        transverse = null_space(divergence)
        scalar = sum(q@q for q in coords) + tide(t, True)*np.eye(n)
        hessian = np.block([[(scalar if a==b else 0.) - coords[a]@coords[b]
                             + 2*commutator(coords[a],coords[b])
                             for b in range(3)] for a in range(3)])
        eigenvalues = np.linalg.eigvalsh(transverse.conj().T @ hessian @ transverse)
        expected = frequency2(t, radius, point)
        np.testing.assert_allclose(eigenvalues[0], expected, atol=4e-12)
        np.testing.assert_allclose(2*(h*np.conj(dh)).imag, 1., atol=2e-9)
        omega = np.sqrt(expected)
        particles = (abs(dh)**2 + expected*abs(h)**2)/(2*omega) - .5
        checks.append(dict(elapsed=t, omega_squared=float(expected),
                           mean_pairs=float(max(0.,particles)),
                           vacuum_probability=float(1/(1+max(0.,particles)))))
    return dict(spin=j, uniform_lower_bound=2/9-1/j, samples=checks)


def thermal_counts(beta_gap):
    scaled = np.array([comb(4,k)**2 * np.exp(2*beta_gap*(k-4)) for k in range(5)])
    return (scaled/scaled.sum()).tolist()


def main():
    radial = [radial_trial(j, DRIFT, True) for j in (16,32,64,128)]
    radial += [radial_trial(16, 0., True), radial_trial(16, DRIFT, False, T_HORIZON)]
    assert all(row["final_gap"]>0 for row in radial[:4])
    assert all(row["final_gap"]<0 for row in radial[-2:])
    mixed = [mixed_trial(16, t, dust) for t, dust in
             [(0., True), (1e-5, True), (1e-4, True), (5e-4, True), (1e-5, False)]]
    np.testing.assert_allclose(mixed[0]["crossing_elapsed"],radial[0]["crossing_elapsed"],atol=1e-9)
    refined = mixed_trial(16,1e-4,True,refine=True)
    np.testing.assert_allclose(refined["final_gap"],mixed[2]["final_gap"],rtol=2e-8,atol=2e-10)
    if refined["crossings"]:
        np.testing.assert_allclose(refined["crossing_elapsed"],mixed[2]["crossing_elapsed"],atol=2e-9)
    late = [mixed_trial(16, t, dust, end=T_HORIZON) for t, dust in
            [(1e-5,True), (1e-4,True), (.001,True), (1e-5,False)]]
    def last_gap(strength, end):
        return mixed_trial(16,strength,True,end=end)["final_gap"]
    thresholds = {name: float(brentq(last_gap, 0., .005, args=(end,), xtol=1e-10))
                  for name,end in [("early",T_END), ("horizon",T_HORIZON)]}
    report = dict(units="u_i=1, R_i=1, initial excess separation=1/4",
                  radial=radial, mixed=mixed, horizon=late, exemplar_zero_gap_strength=thresholds,
                  boson=bosonic_fluctuations(16),
                  thermal_no_pair={str(x):thermal_counts(x)[0] for x in (0.,.5,1.,2.)})
    output = ROOT / "verification/cat-falling-fermi-edge-results.json"
    output.write_text(json.dumps(report, indent=2, allow_nan=False) + "\n", encoding="utf8")
    print("Checked dust and flat evolution, occupied edges, matrix recoil, energy, Gauss law and thermal counts.")


if __name__ == "__main__":
    main()
