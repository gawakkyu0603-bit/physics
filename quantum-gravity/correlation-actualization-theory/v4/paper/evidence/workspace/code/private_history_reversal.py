"""Echo, retained records and repeated returns for the infall contact.

A later operation is always a trace-preserving apparatus when its outcomes are
summed.  The calculation never identifies a later input with an earlier event.
The continuous rotor calculation uses no finite cutoff in layer angle.
"""
from math import erf, exp, pi, sqrt
from pathlib import Path
import json

import numpy as np
from scipy.integrate import quad
from scipy.linalg import expm
from scipy.special import j0

ROOT = Path(__file__).resolve().parents[1]


def scalar_echo():
    """Compare a literal forward/capture/inverse circuit with its Born formula."""
    dim = 7
    neutral = np.eye(dim, dtype=complex)[:, dim // 2]
    exchange = np.diag(np.linspace(.21, .47, dim - 1), 1)
    exchange = exchange + exchange.T
    angle, direction = 2.1, -1
    forward = expm(1j * direction * angle * exchange)
    backward = forward.conj().T
    state = forward @ neutral
    probabilities = abs(state) ** 2
    groups = [[0, 1, 2], [3], [4, 5, 6]]
    def echo(blocks):
        echo_probability = 0.
        for block in blocks:
            selected = np.zeros_like(state)
            selected[block] = state[block]
            echo_probability += abs(np.vdot(neutral, backward @ selected)) ** 2
        weights = [sum(probabilities[block]) for block in blocks]
        assert abs(echo_probability - np.dot(weights, weights)) < 3e-15
        return float(echo_probability)
    full = echo([[n] for n in range(dim)])
    coarse = echo(groups)
    erased_later = sum(abs(np.vdot(neutral, backward[:, n] * state[n])) ** 2
                       for n in range(dim))
    assert abs(erased_later - full) < 2e-15
    # A controlled experiment entirely within one private history. The contact
    # is balanced on the first arm. Copy only the actual transfer mark, then
    # reverse the ordinary Hamiltonians on both arms and trace the mark.
    clean = neutral.copy()
    stored = np.diag(state)
    returned = backward @ stored
    visibility = abs(np.vdot(clean, returned[:, dim // 2]))
    assert abs(visibility - probabilities[dim // 2]) < 3e-15
    return dict(reversible_echo=echo([list(range(dim))]), coarse_echo=coarse,
                fine_echo=full, erased_record_echo=float(erased_later),
                neutral_probability=float(probabilities[dim // 2]),
                both_blank_and_return=float(probabilities[dim // 2] ** 2),
                controlled_visibility=float(visibility),
                best_known_state_visibility=float(sqrt(probabilities[dim // 2])),
                receipt_distribution=probabilities.tolist())


def prefix_channel():
    """A conditional future intervention can change an ancestor proxy, not its prefix."""
    # Two past outcomes, deliberately correlated with the material state.
    born = np.array([.27, .73])
    plus = np.array([1., 1j]) / sqrt(2)
    rho = [np.diag([1., 0.]), np.outer(plus, plus.conj())]
    delay = np.array([[sqrt(.79), sqrt(.21)], [-sqrt(.21), sqrt(.79)]])
    flip = np.array([[0., 1.], [1., 0.]])
    futures = []
    for setting in (np.eye(2), flip):
        weights = np.array([born[h] * np.diag(delay @ setting @ rho[h] @
                                              setting.T @ delay.T).real for h in range(2)])
        assert np.max(abs(weights.sum(axis=1) - born)) < 5e-16
        futures.append(dict(joint=weights.tolist(), past=weights.sum(axis=1).tolist(),
                            past_given_late_click=(weights[:, 1] / weights[:, 1].sum()).tolist()))
    # In a reference-entangled superposition, compare an untouched observer
    # mark with the restored material alone. Perfect record labels are orthogonal.
    zero, one = np.eye(2)
    initial = np.kron(zero, zero)
    later = np.kron(zero, one)
    return dict(future_choices=futures, surroundings_return=1.,
                complete_return=float(abs(np.vdot(initial,later))**2),
                ancestral_flip_pairs=[[0, 1], [1, 0]])


def shared_charge_visits(width=1024.):
    """Normal incident charge X and the continuous angular F=cos(theta) action."""
    def survivor(visits):
        # Even integrand. Panels resolve the Bessel oscillations AND the narrow
        # peak of width 1/sqrt(k); the omitted Gaussian tail is below 4e-33.
        upper = 12 * width
        first = min(1., 8 / sqrt(visits))
        points = [0., first, 1., 4., 12.]
        points.extend(np.arange(16., upper, 16.).tolist())
        points.append(upper)
        points = sorted(set(points))
        integral = 0.
        error = 0.
        def integrand(x):
            return exp(-.5 * (x / width) ** 2) * j0(x) ** (2 * visits)
        for left, right in zip(points, points[1:]):
            area, err = quad(integrand, left, right, epsabs=8e-14, epsrel=4e-11, limit=180)
            integral += area
            error += err
        factor = sqrt(2 / pi) / width
        return integral * factor, error * factor
    one, _ = survivor(1)
    rows = []
    for visits in (1, 2, 4, 16, 64, 256, 1024):
        shared, numerical_error = survivor(visits)
        lower = .5 * erf(1 / (sqrt(2 * visits) * width))
        # Keep the iid alternative in log10 form to avoid underflow.
        assert shared + 1e-15 >= max(one ** visits, lower)
        rows.append(dict(visits=visits, shared=shared, quadrature_error=numerical_error,
                         guaranteed=lower, fresh_log10=visits * float(np.log10(one)),
                         scaled_shared=shared * sqrt(visits) * width))
    return dict(gaussian_width=width, one_pass=one, rows=rows)


def absorbing_loop():
    """An explicit noncommuting quantum continuation and two energy-degenerate exits."""
    survival = np.diag(np.sqrt([.004, .009]))
    mix = expm(1j * .43 * np.array([[0., 1.], [1., 0.]]))
    stay = mix @ survival
    leave = np.diag(np.sqrt(1 - np.diag(survival)**2))
    assert np.linalg.norm(stay.conj().T @ stay + leave.conj().T @ leave - np.eye(2)) < 1e-15
    # Half of a maximally entangled pair keeps a reference outside the process.
    bell = np.eye(2).reshape(-1) / sqrt(2)
    pending = np.outer(bell, bell)
    exited = np.zeros_like(pending, dtype=complex)
    history = []
    for visit in range(1, 17):
        out = np.kron(leave, np.eye(2))
        inside = np.kron(stay, np.eye(2))
        exited += out @ pending @ out.conj().T
        pending = inside @ pending @ inside.conj().T
        rem = float(np.trace(pending).real)
        history.append(rem)
        assert rem <= .009**visit * (1 + 1e-12)
    # On summing all exits, no trace-preserving later choice can change the reference.
    residual = np.trace((exited + pending).reshape(2, 2, 2, 2), axis1=0, axis2=2)
    assert np.linalg.norm(residual - np.eye(2)/2) < 1e-15
    return dict(worst_single_pass=.009, pending=history,
                exterior_plus_survivor_trace=float(np.trace(exited+pending).real),
                reference_error=float(np.linalg.norm(residual-np.eye(2)/2)))


if __name__ == "__main__":
    result = dict(echo=scalar_echo(), prefix=prefix_channel(),
                  persistent=shared_charge_visits(), leakage=absorbing_loop())
    output = ROOT / "verification" / "private-history-reversal-results.json"
    output.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
    print("Return with and without capture:", result["echo"]["fine_echo"], result["echo"]["reversible_echo"])
    print("Shared charge at one and two passages:", [r["shared"] for r in result["persistent"]["rows"][:2]])
