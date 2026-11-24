"""Reproduce Appendix O. The dimensionless examples use m, p and three source weights as measured inputs."""
import json
import math
import os
from itertools import combinations, product
from pathlib import Path

os.environ.setdefault("MPLBACKEND", "Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigh, expm, solve_continuous_lyapunov
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
MASS, MOMENTUM = 2.0, 1.5
WEIGHTS = np.array([1.0, 2.0, 4.0])
ROOT3 = math.sqrt(3)
PROJECTORS = np.array([[[1., 0.], [0., 0.]],
                       [[1., ROOT3], [ROOT3, 3.]],
                       [[1., -ROOT3], [-ROOT3, 3.]]])
PROJECTORS[1:] /= 4


def energy(profile, mass=MASS, momentum=MOMENTUM):
    return momentum ** 2 / (mass + np.sqrt(mass ** 2 + profile * momentum ** 2))


def triangle(weights):
    width = np.linalg.norm(weights - np.roll(weights, -1)) / math.sqrt(2)
    return (weights.sum() - width) / 2, (weights.sum() + width) / 2, width


def probe():
    mass, momentum = MASS, MOMENTUM
    for h in [0., .12, 3., 80.]:
        e = energy(h)
        assert abs(2 * mass * e + h * e * e - momentum ** 2) < 2e-13
    omega8 = 2 * math.pi ** 4.5 / math.gamma(4.5)
    charge = (2 * math.pi) ** 8 / (2 * math.pi * 7 * omega8)
    assert abs(charge / (60 * math.pi ** 3) - 1) < 1e-14
    shell = .7
    def h(z):
        return 1.1 / (z + 1.2) ** 7, 2.3 / (z + 1.5) ** 7
    def k(profile):
        return math.sqrt(2 * mass * shell + shell ** 2 * profile)
    def connected(z):
        a, b = h(z)
        return k(a+b) - k(a) - k(b) + k(0)
    def integrated_derivative(z):
        a, b = h(z)
        def inner(x):
            return quad(lambda y: -(shell ** 4 / 4) / k(x + y) ** 3, 0, b)[0]
        return quad(inner, 0, a)[0]
    shift = quad(connected, 0, .8, epsabs=1e-14)[0]
    derivative = quad(integrated_derivative, 0, .8, epsabs=1e-14)[0]
    assert shift < 0 and abs(shift - derivative) < 5e-16
    return {"pp_charge_over_pi_cubed": charge / math.pi ** 3,
            "two_source_characteristic_difference": shift,
            "integrated_mixed_derivative": derivative}


def graph_checks():
    count, permitted, cases = 0, 0, 0
    vertices = range(4)
    edges = list(combinations(vertices, 2))
    for pattern in product(range(3), repeat=len(edges)):
        weights = np.zeros((4, 4))
        for (i, j), w in zip(edges, pattern):
            weights[i, j] = weights[j, i] = w
        lap = (np.diag(weights.sum(axis=1)) - weights) / 2
        all_twins = True
        for i, j in edges:
            if not weights[i, j]:
                continue
            perm = np.eye(4)
            perm[[i, j]] = perm[[j, i]]
            twins = all(weights[i, k] == weights[j, k] for k in vertices if k not in (i, j))
            assert twins == np.array_equal(perm @ lap, lap @ perm)
            all_twins = all_twins and twins
            cases += 1
        def component(seed):
            reached, frontier = {seed}, {seed}
            while frontier:
                frontier = {int(k) for j in frontier for k in np.flatnonzero(weights[j])} - reached
                reached.update(frontier)
            return reached
        cliques = True
        for i in vertices:
            local_weights = {weights[p, q] for p, q in combinations(component(i), 2)}
            cliques &= not local_weights or (len(local_weights) == 1 and min(local_weights) > 0)
        assert cliques == all_twins
        count += 1
        permitted += int(all_twins)
    return {"four_vertex_weighted_graphs": count, "tested_positive_edges": cases,
            "disjoint_uniform_clique_graphs": permitted}


def shape_response():
    weights = WEIGHTS
    low, high, width = triangle(weights)
    profile = np.einsum("e,eij->ij", weights, PROJECTORS)
    eig, states = eigh(profile)
    assert np.allclose(eig, [low, high])
    quantum_amplitudes = np.array([states[:, 1] @ P @ states[:, 0] for P in PROJECTORS])
    differences = np.roll(weights, -1) - np.roll(weights, -2)
    theory = 3 * differences ** 2 / (16 * width ** 2)
    assert np.allclose(theory, quantum_amplitudes ** 2) and abs(theory.sum() - 3/8) < 1e-14
    q = np.array([.2, -.4, .3])
    gap = energy(low) - energy(high)
    slope = math.sqrt(3) * gap * abs(q @ differences) / (4 * width ** 2)
    def op(values):
        v, u = eigh(np.einsum("e,eij->ij", values, PROJECTORS))
        return (u * energy(v)) @ u.T
    dy = 1e-4
    derivative = (op(weights + dy*q) - op(weights - dy*q)) / (2*dy)
    numeric = abs(states[:, 1] @ derivative @ states[:, 0])
    assert abs(numeric - slope) < 2e-11
    assert abs(differences @ weights) + abs(differences.sum()) < 1e-14
    coeff = MOMENTUM ** 2 / MASS ** 2
    def turning(scale):
        return (math.sqrt(1+coeff*scale*low)-1)*(math.sqrt(1+coeff*scale*high)-1)-2
    sstar = brentq(turning, 0, 100)
    def line(scale):
        return energy(scale * low) - energy(scale * high)
    assert line(sstar) > max(line(.99*sstar), line(1.01*sstar))
    return {"triangle_weights": weights.tolist(), "profile_spectrum": eig.tolist(),
            "individual_transition_strengths": theory.tolist(), "gap": gap,
            "equal_rate_ground_state_power_at_unit_rate": gap * theory.sum(),
            "shape_derivative": slope, "finite_difference_shape_derivative": numeric,
            "scale_at_maximum_gap": sstar, "maximum_gap": line(sstar)}


def wave_transport():
    # The potentials are smooth positive beam envelopes on a longitudinal segment.
    length, shell = 1.7, .74
    def op(z):
        values = np.array([1.1 / (z+1.3) ** 7, 2.7 / (z+1.8) ** 7, .3])
        return np.einsum("e,eij->ij", values, PROJECTORS)
    def rhs(z, state):
        f, df = state[:2], state[2:]
        return np.r_[df, -(2*MASS*shell*np.eye(2)+shell**2*op(z)) @ f]
    start = np.array([1+.2j, .4j, .7j, -.3+.1j])
    solution = solve_ivp(rhs, (0, length), start, t_eval=np.linspace(0, length, 61),
                         rtol=2e-11, atol=2e-13, method="DOP853")
    assert solution.success
    flux = np.imag(np.sum(solution.y[:2].conj()*solution.y[2:], axis=0))
    drift = np.max(np.abs(flux-flux[0]))
    commutator = np.linalg.norm(op(0) @ op(length) - op(length) @ op(0))
    assert commutator > 1e-4 and drift < 1e-9
    # Local constraint exchange in one direction, evaluated independently by finite differences.
    x, t, v, d = .42, .31, .37, 2e-4
    def h(z, tau): return math.exp(-(z-v*tau)**2)
    def lam(z): return math.exp(-.6*(z+.23)**2)
    def dz(f, z): return (f(z+d)-f(z-d))/(2*d)
    # Use analytic derivatives for the individual manufactured fields. Differentiate the
    # assembled flux only once, so machine-dependent rounding is not amplified three times.
    def hx(z): return -2*(z-v*t)*h(z,t)
    def hxx(z): return (4*(z-v*t)**2-2)*h(z,t)
    def lx(z): return -1.2*(z+.23)*lam(z)
    def lxx(z): return (1.44*(z+.23)**2-1.2)*lam(z)
    def hdot(z): return -v*hx(z)
    def source(z): return -hxx(z)
    def current(z): return v*source(z)
    def energy_flux(z): return -hdot(z)*lx(z)-v*lam(z)*hxx(z)-lam(z)*current(z)
    energy_res = dz(energy_flux,x) + lxx(x)*hdot(x) + current(x)*lx(x)
    def stress(z): return hx(z)*lx(z)
    momentum_res = dz(stress,x)-lxx(x)*hx(x)+source(x)*lx(x)
    assert max(abs(energy_res), abs(momentum_res)) < 2e-6
    return {"stationary_flux_drift": drift, "profile_commutator_norm": commutator,
            "manufactured_local_energy_residual": energy_res,
            "manufactured_local_momentum_residual": momentum_res}


def transported_mark():
    eye = np.eye(2)
    J = np.array([[0., 1.], [-1., 0.]])
    base, radius, width = 1.4, .56, .11
    def profile(theta, epsilon):
        offsets = np.array([0., -2*math.pi/3, 2*math.pi/3])
        w = base + epsilon*np.cos(theta+offsets)
        dw = -epsilon*np.sin(theta+offsets)
        return np.einsum("i,ijk->jk", w, PROJECTORS), np.einsum("i,ijk->jk", dw, PROJECTORS)
    def mark(theta, epsilon):
        X, dX = profile(theta, epsilon)
        vals, vecs = eigh(X)
        hi = vecs[:,1]
        P = np.outer(hi,hi)
        dP = ((eye-P) @ dX @ P + P @ dX @ (eye-P))/(vals[1]-vals[0])
        A = P @ dP - dP @ P
        return P, dP, A, energy(vals[0])-energy(vals[1])
    P, dP, A, gap = mark(.37, radius)
    assert np.allclose(dP + A @ P - P @ A, 0.) and np.allclose(A, J/2)
    ratio = width**2/(gap**2+width**2)
    f = 1-ratio
    def rhs(theta, flat):
        return (-f * mark(theta, radius)[2] @ flat.reshape(2,2)).ravel()
    sol = solve_ivp(rhs,(0.,2*math.pi),eye.ravel(),rtol=1e-11,atol=1e-13,method="DOP853")
    assert sol.success
    U = sol.y[:,-1].reshape(2,2)
    trace = float(np.trace(U)/2)
    bare = np.linalg.norm(dP)
    fraction = np.linalg.norm(dP+f*(A@P-P@A))/bare
    assert abs(fraction-ratio)<1e-14 and abs(trace+math.cos(math.pi*fraction))<1e-10
    sample_even = quad(lambda t: width*math.exp(-width*t)*math.cos(gap*t),0,np.inf)[0]
    assert abs(sample_even-ratio)<2e-10
    def filter_at(epsilon):
        _, _, _, d = mark(.37, epsilon)
        return d**2/(d**2+width**2)
    small = filter_at(.0001)/filter_at(.0002)
    assert abs(small-.25) < 1e-6
    return {"line_gap": gap, "linewidth": width, "ordinary_to_smoothed_amplitude_fraction": fraction,
            "half_trace_after_one_turn": trace, "trace_identity_residual": trace+math.cos(math.pi*fraction),
            "even_exponential_response": sample_even, "halved_radius_filter_ratio": small}


def mediator():
    # Each stable positive metric oscillator contributes a positive residue at imaginary frequency.
    couplings = np.array([[1., -.4], [.64, 1.2], [-.5, .7]])
    frequencies = np.array([.8, 1.6, 2.5])
    xi = .47
    weighted = couplings / np.sqrt(xi**2 + frequencies[:, None]**2)
    gram = weighted.T @ weighted
    minors = sum((row[0]*col[1]-row[1]*col[0])**2 for row, col in combinations(weighted, 2))
    assert abs(np.linalg.det(gram)-minors) < 1e-13
    pure_cross = np.linalg.eigvalsh([[0., gram[0,1]], [gram[0,1], 0.]])
    assert min(pure_cross) < 0
    return {"imaginary_frequency": xi, "kernel": gram.tolist(), "gram_determinant": minors,
            "pure_cross_minimum_eigenvalue": pure_cross[0]}


def receiver():
    coupling, detune, k_g, k_other = .23, .17, .41, .19
    width = k_g + k_other
    A = np.array([[0, -1j*coupling], [-1j*coupling, -width/2-1j*detune]])
    initial = np.diag([1., 0.])
    dwell = solve_continuous_lyapunov(A, -initial)
    moment = solve_continuous_lyapunov(A, -dwell)
    probability = float(k_g * dwell[1,1].real)
    mean = float(moment[1,1].real / dwell[1,1].real)
    expected = 2/width + (detune**2 + width**2/4)/(width*coupling**2)
    assert abs(probability - k_g/width) < 1e-12 and abs(mean - expected) < 1e-11
    tau = np.linspace(0, 100, 4001)
    density = k_g * np.array([abs((expm(A*t) @ np.array([1,0]))[1])**2 for t in tau])
    assert abs(np.trapezoid(density, tau)-probability) < 1e-6
    return {"gravitational_branch_probability": probability, "conditional_mean_time": mean,
            "conditional_mean_time_formula": expected, "initial_density": density[0]}


def figure(results):
    scale = np.geomspace(.01, 500, 301)
    lo, hi = results["triangle"]["profile_spectrum"]
    curve = energy(scale*lo)-energy(scale*hi)
    fig, axes = plt.subplots(1, 2, figsize=(8.1, 3.0), layout="constrained")
    axes[0].semilogx(scale, curve, color="#155277", lw=2)
    axes[0].plot(results["triangle"]["scale_at_maximum_gap"], results["triangle"]["maximum_gap"], "o", color="#a14425")
    axes[0].set(xlabel="Common multiplier of source strengths", ylabel="Spectral gap (energy units)")
    amps = results["triangle"]["individual_transition_strengths"]
    axes[1].bar(["12", "23", "31"], amps, color=["#155277", "#a14425", "#43826c"], width=.6)
    axes[1].set(xlabel="Contact selected by the apparatus", ylabel="Squared transition amplitude", ylim=(0,.27))
    for ax in axes: ax.grid(axis="y", alpha=.2)
    dest = ROOT/"manuscripts"/"overlapping_gravitational_contacts.pdf"
    dest.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(dest, metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    out = {"probe": probe(), "graphs": graph_checks(), "triangle": shape_response(),
           "wave": wave_transport(), "mediator": mediator(), "transport": transported_mark(), "receiver": receiver()}
    figure(out)
    dest = ROOT/"verification"/"overlapping-contact-results.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(out, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    print(json.dumps(out, indent=2))
