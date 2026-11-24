"""Real-frequency gravitational transport and two observers' record probabilities."""
from pathlib import Path
import json
import math
import os

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
EYE = np.eye(2)
SQRT3 = np.sqrt(3.0)


def coefficients(degree, coupling, pure_gravity):
    """Coefficients of V/f in inverse powers of areal radius. M=1."""
    angular = degree * (degree + 1)
    if pure_gravity:
        other = (degree + 1) * (degree + 2)
        return {2: np.diag([angular, other]), 3: -6 * EYE}
    mix = 6 * coupling * math.sqrt(angular * (angular - 2))
    return {2: angular * EYE, 3: np.diag([-6., 2.]),
            5: np.array([[0., mix], [mix, 0.]]),
            8: np.diag([0., 36 * angular * coupling**2])}


def infinity_wave(w, radius, potential, order):
    """Outgoing Jost column exp(i*w*x) times an inverse-radius series."""
    terms = [EYE.astype(complex)]
    for n in range(1, order + 1):
        coeff = (n - 1) * n * terms[n - 1]
        if n >= 2:
            coeff = coeff - 2 * (n - 2) * n * terms[n - 2]
        for power, matrix in potential.items():
            if n + 1 >= power:
                coeff = coeff - matrix @ terms[n + 1 - power]
        terms.append(coeff / (2j * w * n))
    series = sum(term / radius**n for n, term in enumerate(terms))
    radial_derivative = sum(-n * term / radius**(n + 1) for n, term in enumerate(terms))
    tortoise = radius + 2 * np.log(radius / 2 - 1)
    phase = np.exp(1j * w * tortoise)
    return np.stack([phase * series, phase * (1j*w*series + (1-2/radius)*radial_derivative)])


def scattering(w, coupling=0.0, pure_gravity=False, refined=False):
    """Two flux-normalised channels at each of infinity and the horizon."""
    potential = coefficients(2, coupling, pure_gravity)
    outer, order, inner = (110., 13, -32.) if refined else (80., 10, -28.)
    rtol = 1.5e-12 if refined else 1.0e-11
    ym = np.log(6 / 2 - 1)

    def propagate(y0, columns):
        def ode(y, flat):
            radius = 2 * (1 + np.exp(y))
            f = np.exp(y) / (1 + np.exp(y))
            v = f * sum(a / radius**k for k, a in potential.items())
            phi, momentum = flat.reshape(2, 2, 2)
            return np.stack([radius * momentum, radius * ((v-w*w*EYE) @ phi)]).ravel()

        solution = solve_ivp(ode, (y0, ym), columns.ravel(), method="DOP853",
                             atol=rtol * 0.01, rtol=rtol)
        if not solution.success:
            raise ArithmeticError(solution.message)
        return solution.y[:, -1].reshape(4, 2)

    x_left = 2*(1+np.exp(inner)) + 2*inner
    phase = np.exp(-1j*w*x_left)
    into_horizon = propagate(inner, np.stack([phase*EYE, -1j*w*phase*EYE]))
    to_infinity = propagate(np.log(outer/2-1), infinity_wave(w, outer, potential, order))
    # Unknown outgoing amplitudes (infinity,horizon). Incoming columns in the same order.
    return np.linalg.solve(np.column_stack([to_infinity, -into_horizon]),
                           np.column_stack([-to_infinity.conj(), into_horizon.conj()]))


def spectrum(scatter, frequency):
    r = scatter[:2, :2]
    transmit = scatter[:2, 2:]
    emission = transmit @ transmit.conj().T
    absorb = EYE - r.conj().T @ r
    n = 1 / np.expm1(8*np.pi*frequency)
    cross = emission[0, 1]
    gap = np.diff(np.linalg.eigvalsh(emission))[0]
    tilt = 2*abs(cross)/gap
    return dict(emissivity=[emission[0, 0].real, emission[1, 1].real],
                cross=[cross.real, cross.imag], thermal_occupation=n,
                covariance=n*n*abs(cross)**2, normalized_tilt=tilt,
                unitarity=np.max(abs(scatter.conj().T @ scatter-np.eye(4))),
                reciprocity=np.max(abs(scatter-scatter.T)),
                kirchhoff=np.max(abs(emission-absorb.T)))


def reader(scatter, angle):
    """Helstrom operator in vacuum + two one-particle modes, no heralding."""
    transmit = scatter[:2, 2:]
    gram = transmit.conj().T @ transmit
    eigenvalues, axes = np.linalg.eigh(gram)
    low, high = eigenvalues
    rotation = np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])
    packets = transmit @ axes[:, ::-1] @ rotation
    lengths = np.sum(abs(packets)**2, axis=0)
    states = []
    for i in (0, 1):
        state = np.zeros((3, 3), complex)
        state[0, 0] = 1 - lengths[i]
        state[1:, 1:] = np.outer(packets[:, i], packets[:, i].conj())
        states.append(state)
    guess = .5 + np.sum(abs(np.linalg.eigvalsh(states[0]-states[1])))/4
    split = abs((high-low)*np.cos(2*angle))
    analytic = .5 + (split + np.sqrt(4*high*low+split**2))/4
    assert abs(guess-analytic) < 1e-12
    return dict(transmissions=[low, high], guess=guess, uncertainty_bits=-np.log2(guess),
                mean_escape=float(np.mean(lengths)), disagreement=1-guess)


def unambiguous_balanced(low, high):
    """Optimal conclusive test for equiprobable equal-norm transmitted pure states."""
    packets = np.array([[np.sqrt(high), np.sqrt(high)], [np.sqrt(low), -np.sqrt(low)]])/np.sqrt(2)
    norm = np.sqrt((low+high)/2)
    states = packets/norm
    overlap = abs((states.T @ states)[0, 1])
    orthogonal = np.array([[0., -1.], [1., 0.]]) @ states[:, ::-1]
    effects = [np.outer(u, u)/(1+overlap) for u in orthogonal.T]
    probs = np.array([np.sum(packets * (effect @ packets), axis=0) for effect in effects])
    assert np.min(np.linalg.eigvalsh(EYE-sum(effects))) > -1e-12
    assert abs(probs[1, 0])+abs(probs[0, 1]) < 1e-13
    return float(np.trace(probs)/2)


def matrix_lines():
    """Exact centre-of-mass transitions of the plane-wave U(N) matrix Hamiltonian."""
    # Units mu=6, mass of the canonically normalised oscillators=1.
    hot, cool, beta = 2., 1., .7
    nh, nc = (1/np.expm1(beta*om) for om in (hot, cool))
    weights = [(2*hot, (nh+1)**2/(2*hot**2), nh**2/(2*hot**2)),
               (2*cool, (nc+1)**2/(2*cool**2), nc**2/(2*cool**2)),
               (hot+cool, (nh+1)*(nc+1)/(2*hot*cool), nh*nc/(2*hot*cool))]
    # First two tensors are (x1^2-x2^2)/sqrt(2) for two equal-frequency axes.
    # The third is sqrt(2)*xh*xc. Common gravitational normalisation cancels.
    directions = np.array([[1., 0.], [-.5, SQRT3/2], [-.5, -SQRT3/2]])
    result = []
    for v, (w, up, down) in zip(directions, weights):
        port = np.sqrt(2/3)*v
        assert abs(down-up*np.exp(-beta*w)) < 2e-15
        result.append(dict(frequency=w, up=(up*np.outer(port, port)).tolist(),
                           down=(down*np.outer(port, port)).tolist()))
    # Independent number-state summation, with finite tail well below output precision.
    for om, up, down in [(hot, weights[0][1], weights[0][2]), (cool, weights[1][1], weights[1][2])]:
        n = np.arange(80)
        p = -np.expm1(-beta*om)*np.exp(-beta*om*n)
        assert abs(up-np.dot(p, (n+1)*(n+2))/(4*om**2)) < 1e-13
        assert abs(down-np.dot(p, n*(n-1))/(4*om**2)) < 1e-13
    for sign, expected in [(1, weights[2][1]), (0, weights[2][2])]:
        factors = []
        for om in (hot, cool):
            n = np.arange(80)
            factors.append(np.dot(-np.expm1(-beta*om)*np.exp(-beta*om*n), n+sign))
        assert abs(np.prod(factors)/(2*hot*cool)-expected) < 1e-13
    axes = np.column_stack([2*directions[:, 0]*directions[:, 1],
                            directions[:, 0]**2-directions[:, 1]**2])
    return dict(beta_mu=6*beta, lines=result,
                optimal_worst_gap_fraction=float(np.max(np.sqrt(1-(axes @ axes[0])**2))))


def shell_geometry():
    """Two static, positive-energy shells with the same exterior mass M=1."""
    radius, event_radius = 10., 1.3
    outside = np.sqrt(1-2/radius)
    branches = []
    for core in (.5, .8):
        inside = np.sqrt(1-2*core/radius)
        mass = radius*(inside-outside)
        density = mass/(4*np.pi*radius**2)
        pressure = density*(1/(inside*outside)-1)/4
        stiffness = 4*np.pi*radius**4*pressure
        dust = mass-stiffness/radius**2
        first = -2*stiffness/radius**3
        second = 6*stiffness/radius**4
        gap = 1-core
        h = gap/mass + mass/(2*radius)
        dh = -gap*first/mass**2+first/(2*radius)-mass/(2*radius**2)
        ddh = -gap*(second/mass**2-2*first**2/mass**3)
        ddh += second/(2*radius)-first/radius**2+mass/radius**3
        force = 2*core/radius**2-2*h*dh
        frequency_sq = -2*core/radius**3-dh**2-h*ddh
        def effective_potential(r):
            s = dust + stiffness/r**2
            return 1-2*core/r-(gap/s+s/(2*r))**2
        step = .01
        numeric = (effective_potential(radius+step)+effective_potential(radius-step)
                   -2*effective_potential(radius))/(2*step**2)
        assert abs(effective_potential(radius))+abs(force) < 2e-14
        assert abs(numeric-frequency_sq) < 5e-9 and frequency_sq > 0
        assert 0 < pressure < density and dust > 0
        branches.append(dict(core_mass=core, dust=dust, stiffness=stiffness,
                             pressure_over_density=pressure/density, radial_frequency_sq=frequency_sq,
                             trapping_scalar=1-2*core/event_radius, stretching=2*core/event_radius**3))
    gap = branches[1]["stretching"]-branches[0]["stretching"]
    overlap = np.exp(-2.)  # a local pointer displacement of four standard deviations
    guess = (1+np.sqrt(1-overlap**2))/2
    # The same freely falling dust shell in both alternatives. Set v=0 on the
    # ingoing null sheet that crosses the shell at the chosen launch radius.
    rest_mass = .19
    low_core = branches[0]["core_mass"]
    def dv_inward(r):
        h = (1-low_core)/rest_mass+rest_mass/(2*r)
        speed = np.sqrt(h*h-1+2*low_core/r)
        return 1/(speed*(h+speed))
    def light_arrival(r):
        return 2*(r-event_radius+2*low_core*np.log((r-2*low_core)/(event_radius-2*low_core)))
    def shell_arrival(r, launch):
        return quad(dv_inward, r, launch, epsabs=1e-12, epsrel=1e-12)[0]
    critical = brentq(lambda launch: shell_arrival(2., launch)-light_arrival(2.), 10., 100.)
    launches = []
    for launch in (10., 100.):
        meet = brentq(lambda r: shell_arrival(r, launch)-light_arrival(r), event_radius, launch)
        launches.append(dict(launch=launch, low_core_shell_at_two=shell_arrival(2., launch),
                             low_core_light_at_two=light_arrival(2.), meeting_radius=meet,
                             low_core_escape=bool(meet>2.)))
    assert launches[0]["meeting_radius"] < 2 < launches[1]["meeting_radius"]
    return dict(shell_radius=radius, areal_event=event_radius, branches=branches,
                infalling_dust=dict(rest_mass=rest_mass, critical_launch=critical, launches=launches),
                local_overlap=overlap, local_guess=guess, distant_guess=.5,
                local_variance=gap**2*guess*(1-guess), distant_variance=gap**2/4,
                variance_ratio=overlap**2, certified_local=1-overlap, certified_distant=0.)


def terminal_records():
    """Four occupied late packets, one polarization qubit per packet."""
    v = np.zeros((16, 2))
    v[[0, 15], 0] = 1/np.sqrt(2)
    v[[3, 12], 1] = 1/np.sqrt(2)
    z = np.diag([1., -1.])
    x = np.array([[0., 1.], [1., 0.]])
    def at_sites(op, sites):
        product = np.ones((1, 1))
        for site in range(4):
            product = np.kron(product, op if site in sites else EYE)
        return product
    for j in range(4):
        for op in (x, z, 1j*x@z):
            assert np.max(abs(v.T @ at_sites(op, [j]) @ v)) < 1e-14
    assert np.allclose(at_sites(z, [0, 2]) @ v, v @ z)
    for sites in ([0, 1], [2, 3]):
        assert np.allclose(at_sites(x, sites) @ v, v @ x)
    plus = v @ np.array([1., 1.])/np.sqrt(2)
    rho = np.outer(plus, plus)
    def written(state, site):
        sign = at_sites(z, [site])
        return (state + sign @ state @ sign)/2
    single = written(rho, 2)
    double = written(single, 0)
    probe = at_sites(x, [0, 1])
    # A classical list of all asymptotic energy losses can coexist with a
    # quantum polarization code. Positive per-step weights need not be thermal.
    def histories(remaining, record, weight):
        if remaining == 0:
            yield record, weight
            return
        choices = list(range(1, min(3, remaining)+1))
        counts = (1, 2, 1)[:len(choices)]
        for jump, count in zip(choices, counts):
            yield from histories(remaining-jump, record+(jump,), weight*count/sum(counts))
    all_histories = list(histories(12, (), 1.))
    assert all(sum(losses)==12 and len(losses)>=4 for losses, _ in all_histories)
    assert abs(math.fsum(prob for _, prob in all_histories)-1) < 1e-14
    bell = np.array([1., 0., 0., 1.])/np.sqrt(2)
    replacement = np.array([[.4, .1j], [-.1j, .6]])
    constant_fidelity = np.vdot(bell, np.kron(EYE/2, replacement) @ bell).real
    assert abs(constant_fidelity-.25)<1e-15
    dv = quad(lambda y: 4*y**3/(1+y), 0., 1.)[0]
    assert abs(dv-(10/3-4*np.log(2))) < 1e-14
    contact = []
    for rate in (0., 1., 20.):
        flip, duration = 1., 2.
        bias = np.exp(-(rate+2*flip)*duration)
        bias += quad(lambda age: rate*np.exp(-(rate+2*flip)*age), 0., duration)[0]
        error = flip/(rate+2*flip)*(-np.expm1(-(rate+2*flip)*duration))
        assert abs((1-bias)/2-error) < 2e-15
        contact.append(dict(arrivals_per_flip=rate, error=error))
    return dict(horizon_to_end_proper_time_over_mass=4/3, last_advanced_interval_over_mass=dv,
                complete_energy_histories=len(all_histories), least_slots=min(len(h) for h, _ in all_histories),
                fidelity_with_four_percent_unique_sectors=.96+.04*constant_fidelity,
                earlier_link_errors=contact,
                exterior_phase_after_one_write=np.trace(probe @ single),
                exterior_phase_after_two_writes=np.trace(probe @ double))


def plot_geometry(geometry):
    os.environ.setdefault("MPLCONFIGDIR", str(ROOT/".research-tools"/"mpl-reciprocal-gravity"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.3, 3.2), layout="constrained")
    rstar = geometry["areal_event"]
    r = np.linspace(rstar, 3.7, 220)
    light = 2*(r-rstar+np.log((r-1)/(rstar-1)))
    left.plot(r, light, color="#132e50", label="Outgoing signal")
    for launch, color in zip(geometry["infalling_dust"]["launches"], ["#b95217", "#16817a"]):
        def travel(rad):
            h = .5/.19+.19/(2*rad)
            u = np.sqrt(h*h-1+1/rad)
            return 1/(u*(h+u))
        arrival = [quad(travel, point, launch["launch"])[0] for point in r]
        left.plot(r, arrival, color=color, label=fr"Shell, $R_0/M={launch['launch']:.0f}$")
        meet = launch["meeting_radius"]
        left.plot(meet, 2*(meet-rstar+np.log((meet-1)/(rstar-1))), "o", color=color)
    left.axvline(2., color="0.45", ls=":", lw=1)
    left.set(xlabel="Areal radius $r/M$", ylabel="Interior advanced time $v/M$", xlim=(1.25, 3.7))
    left.legend(fontsize=8)
    separation = np.linspace(0, 5., 180)
    k = np.exp(-separation**2/8)
    right.plot(separation, (1+np.sqrt(1-k*k))/2, color="#132e50", label="A, best binary guess")
    right.plot(separation, 1-k, color="#b95217", label="A, certain identification")
    right.axhline(.5, color="#16817a", ls="--", label="B, best guess before news")
    right.set(xlabel="Local pointer separation / rms width", ylabel="Probability", ylim=(-.03, 1.04))
    right.legend(fontsize=8, loc="lower right")
    fig.savefig(ROOT/"manuscripts"/"relative_black_hole_geometry.pdf", metadata={"CreationDate": None})
    plt.close(fig)


def main():
    gravity, conversion = {}, {}
    errors = []
    for w in (.25, .35, .45, .55):
        s = scattering(w, pure_gravity=True)
        precise = scattering(w, pure_gravity=True, refined=True)
        errors.append(float(np.max(abs(s-precise))))
        axial, balanced = reader(precise, 0.), reader(precise, np.pi/4)
        low, high = balanced["transmissions"]
        usd = unambiguous_balanced(low, high)
        assert abs(usd-low) < 1e-12
        gravity[str(w)] = dict(eigenbasis=axial, balanced=balanced,
                               certified_balanced=usd, certified_eigenbasis=(low+high)/2)
    for w in (.25, .35, .45):
        for a in (0., .05, .1):
            s = scattering(w, a)
            precise = scattering(w, a, refined=True)
            errors.append(float(np.max(abs(s-precise))))
            data = spectrum(precise, w)
            assert max(data[k] for k in ("unitarity", "reciprocity", "kirchhoff")) < 2e-9
            conversion[f"{w},{a}"] = data
    assert max(errors) < 2e-7
    geometry = shell_geometry()
    result = dict(pure_gravity=gravity, coupled_fields=conversion, matrix_model=matrix_lines(),
                  geometry_records=geometry, terminal_records=terminal_records(),
                  largest_boundary_refinement=max(errors))
    plot_geometry(geometry)
    (ROOT/"verification"/"reciprocal-gravity-record-results.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False)+"\n", encoding="utf8")
    print("Two exterior channels, four gravitational bands and three matrix transitions checked.")
    print("Maximum change of complex scattering amplitude on refinement:", max(errors))


if __name__ == "__main__":
    main()
