"""A tidal transition out of the normalized SU(2) BFSS threshold state.

Use the full relative momentum cover, with plane waves exp(i k.r) and H=p^2.
The core comparison is a solvable exterior boundary problem, not BFSS data.
"""
import json
import math
from fractions import Fraction
from itertools import product
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from numpy.polynomial import Polynomial
from scipy.integrate import quad
from scipy.special import gamma, jv, yv

ROOT = Path(__file__).resolve().parents[1]
DIM = 9
SPHERE_AREA = 32 * math.pi**4 / 105
TAIL_COUPLING = 16 * math.pi**2


def polarizations():
    """Three linearly independent tensor sectors relative to the ninth axis."""
    modes = []
    for first, second in ((0, 1), (0, 8)):
        tensor = np.zeros((DIM, DIM))
        tensor[first, second] = tensor[second, first] = 1 / math.sqrt(2)
        modes.append(tensor)
    modes.append(np.diag([-1.] * 8 + [8.]) / math.sqrt(72))
    return modes


def radial_fourier_polynomial(left, right):
    # Contract rhat with each tensor first. The transverse direction is on S^7.
    z = Polynomial([0, 1])
    transverse = 1 - z**2
    left_normal, right_normal = left[-1, -1], right[-1, -1]
    left_t, right_t = left[:-1, :-1], right[:-1, :-1]
    left_trace, right_trace = np.trace(left_t), np.trace(right_t)
    mixed = (left_normal * right_trace + right_normal * left_trace
             + 4 * np.dot(left[:-1, -1], right[:-1, -1]))
    tangent = left_trace * right_trace + 2 * np.trace(left_t @ right_t)
    angular = (left_normal * right_normal * z**4 + mixed * z**2 * transverse / 8
               + tangent * transverse**2 / 80)
    return transverse**3 * angular


def angular_checks():
    directions = polarizations()
    reflector = np.diag([1.] * 8 + [-1.])
    checks = []
    for i, left in enumerate(directions):
        for j, right in enumerate(directions):
            weight = radial_fourier_polynomial(left, right)
            derivative = weight.deriv()
            # weight is even; division by z has no remainder.
            quotient, remainder = divmod(derivative, Polynomial([0, 1]))
            assert np.max(np.abs(remainder.coef)) < 2e-15
            integral = quotient.integ()
            limit = -(315 / 64) * (integral(1) - integral(-1))
            expected = np.trace(right @ reflector @ left @ reflector)
            assert abs(limit - expected) < 2e-13
            if i == j:
                regularized = []
                for ratio in (0.1, 0.01, 0.001):
                    value = -2 * (315 / 64) * quad(
                        lambda z: derivative(z) * z / (z*z + ratio*ratio),
                        0, 1, epsabs=1e-12)[0]
                    regularized.append(value)
                checks.append(dict(component=["transverse", "mixed", "axial"][i],
                                   analytic=expected, position_integral=limit,
                                   regulator_values=regularized))
    # Independent directional second differences of the Fourier state.
    direction = np.arange(1., 10.)
    direction /= np.linalg.norm(direction)
    tensor = directions[0] / math.sqrt(5) + directions[2] * 2 / math.sqrt(5)
    eigenvalues, axes = np.linalg.eigh(tensor)
    projection = lambda x: np.outer(x, x) / np.dot(x, x)
    step = 0.00022
    hessian = np.zeros_like(tensor)
    for value, axis in zip(eigenvalues, axes.T):
        hessian += value * (projection(direction + step*axis)
                            - 2*projection(direction) + projection(direction - step*axis)) / step**2
    reflection = np.eye(DIM) - 2 * np.outer(direction, direction)
    hessian_error = np.linalg.norm(hessian/2 - reflection @ tensor @ reflection)
    assert hessian_error < 2e-7
    return dict(position_space=checks, momentum_hessian_residual=hessian_error)


def hard_core_checks():
    """Scattering off a Dirichlet sphere, compared to zero-core Bessel moments."""
    rows = []
    for ell in (0, 2, 4):
        order = ell + 3.5
        free = 2**(-2.5) * gamma((ell+2)/2) / gamma((ell+7)/2)
        # Tail beyond 700 of x^(-5/2)J_nu is below the precision used here.
        numerical_free = quad(lambda x: x**(-2.5)*jv(order, x), 0, 700,
                              limit=400, epsabs=3e-13)[0]
        assert abs(numerical_free-free) < 1.5e-8
        rows_at_ell = []
        for ka in (0.5, 0.25, 0.125):
            phase = math.atan(jv(order, ka)/yv(order, ka))
            # Integrate the *difference* to avoid subtracting two close transfers.
            missing = -quad(lambda x: x**(-2.5)*jv(order, x), 0, ka)[0]
            irregular = -math.sin(phase) * (
                quad(lambda x: x**(-2.5)*yv(order, x), ka, 1, epsabs=2e-12)[0] +
                quad(lambda x: x**(-2.5)*yv(order, x), 1, 700, limit=400, epsabs=1e-12)[0])
            difference = missing * math.cos(phase) - 2*math.sin(phase/2)**2*free + irregular
            rows_at_ell.append(dict(ka=ka, fractional_change=difference/free))
        previous, last = [abs(x["fractional_change"]) for x in rows_at_ell[-2:]]
        exponent = math.log2(previous/last)
        assert abs(exponent-ell-2) < .04
        rows.append(dict(ell=ell, free_moment=free, truncated_free=numerical_free,
                         exponent=exponent, samples=rows_at_ell))
    return rows


def spectral_checks():
    density = SPHERE_AREA*TAIL_COUPLING**2/(8*(2*math.pi)**9)
    assert math.isclose(density, 2/(105*math.pi), rel_tol=1e-14)
    euclidean = quad(lambda e: density*e**1.5*math.exp(-e), 0, 80)[0]
    assert abs(euclidean-1/(70*math.sqrt(math.pi))) < 4e-11
    duration = 3.
    # Unit strain amplitude. f = -h''/2 for a returning, linearly polarized pulse.
    def spectrum(e):
        return density * e**1.5 * (2*math.pi*duration**2)*e**4/4 * math.exp(-(duration*e)**2)
    escape = quad(spectrum, 0, 5, epsabs=1e-14)[0]
    work = quad(lambda e: e*spectrum(e), 0, 5, epsabs=1e-14)[0]
    assert math.isclose(escape, gamma(13/4)/210 / duration**4.5, rel_tol=1e-11)
    assert math.isclose(work/escape, gamma(15/4)/(gamma(13/4)*duration), rel_tol=1e-11)
    cuts = (.00, .25, .5, .75, 1.)
    caps = [2*quad(lambda z: (35/32)*(1-z*z)**3, cut, 1)[0] for cut in cuts]
    assert all(abs(prob-(1-35/16*(z-z**3+3*z**5/5-z**7/7))) < 2e-14
               for z, prob in zip(cuts, caps))
    return dict(density=density, euclidean=euclidean, strain_coefficient=gamma(13/4)/210,
                mean_energy_times_duration=duration*work/escape, caps=list(zip(cuts, caps)))


def superspin_checks():
    """Project the privately dephased angular state on two Ward-basis harmonics."""
    density = lambda z: 35/32 * (1-z*z)**3
    harmonic = lambda z: math.sqrt(11)/4 * (9*z*z-1)
    assert abs(quad(lambda z: density(z)*harmonic(z), -1, 1)[0]) < 2e-15
    assert abs(quad(lambda z: density(z)*harmonic(z)**2, -1, 1)[0]-1) < 2e-14
    rows = []
    for cut in (.25, .5, .75):
        cap = 2*quad(density, cut, 1)[0]
        moment = 2*quad(lambda z: density(z)*harmonic(z), cut, 1)[0]
        weight = 2*moment**2
        assert abs(weight-(13475/2048)*cut**2*(1-cut**2)**8) < 1e-14
        assert weight <= 2*cap*(1-cap)
        rows.append(dict(cut=cut, cap=cap, superspin_zero=cap**2+(1-cap)**2,
                         superspin_two=weight))
    return rows


def encounter_instrument():
    # Three elastic eigenphases. An independent, coherent density matrix exposes
    # the cross-channel effect that an elastic eigenstate alone cannot reveal.
    phases = np.array([.07, -.11, .21])
    scattering = np.diag(np.exp(1j*phases))
    cosine = (scattering+scattering.conj().T)/2
    sine = (scattering-scattering.conj().T)/(2j)
    assert np.allclose(cosine@cosine+sine@sine, np.eye(3))
    state = np.array([1., 1j, -2.]) / math.sqrt(6)
    rho = np.outer(state, state.conj())
    written = cosine@rho@cosine+sine@rho@sine
    kernel = np.cos(phases[:, None]-phases[None, :])
    assert np.allclose(written, kernel*rho) and np.linalg.eigvalsh(written).min()>-1e-14
    # Compare one shared write with independent encounters on two separated pairs.
    a, b = phases[0]-phases[1], phases[1]-phases[2]
    common = math.cos(a+b)
    independent = math.cos(a)*math.cos(b)
    assert abs(common-independent+math.sin(a)*math.sin(b)) < 1e-14
    click = Fraction(2, 180)**2
    loss = 2*(Fraction(1, 180)-Fraction(1, 5040))**2
    return dict(completeness=float(np.max(np.abs(cosine@cosine+sine@sine-np.eye(3)))),
                shared_coherence=common, independent_coherence=independent,
                singlet_click_coefficient=str(click), lost_coherence_coefficient=str(loss))


def continuous_layers():
    """Refinement of Born bins, a continuum of first-entry times, and joint stress."""
    density = lambda u: 35/16*(1-u*u)**3
    square_mass = quad(lambda u: density(u)**2, 0, 1, epsabs=1e-13)[0]
    assert abs(square_mass-700/429) < 2e-14
    refinements = []
    for bins in (4, 16, 64, 256):
        weights = [quad(density, j/bins, (j+1)/bins)[0] for j in range(bins)]
        retained = sum(p*p for p in weights)
        assert abs(sum(weights)-1) < 2e-14
        refinements.append(dict(bins=bins, retained=retained, scaled=bins*retained))
    assert abs(refinements[-1]["scaled"]-square_mass) < 2e-5
    rates = np.array([28.**2, 1.])
    overlap = quad(lambda t: math.sqrt(rates.prod())*math.exp(-rates.sum()*t/2),
                   0, .2)[0]
    assert abs(overlap-56/785) < 3e-14
    # Unit mean time for the slow channel. Distinct initial Born weights are recovered
    # after integrating all first-entry densities, even with a never-written sector.
    birth_weights = np.array([.23, .51, .26])
    active = [quad(lambda t: w*r*math.exp(-r*t), 0, 60/r)[0]
              for w, r in zip(birth_weights, rates)]
    assert np.allclose(active, birth_weights[:2]) and abs(sum(active)+birth_weights[2]-1)<1e-13
    # A resolved response vector may have phase as well as likelihood. Compare
    # direct projections with the two-copy variance for a complex normalized mark.
    axes = np.linspace(-1, 1, 11)
    weights = (1-axes**2)**3
    weights /= weights.sum()
    marks = np.stack((np.cos(axes), np.sin(axes)*np.exp(1j*axes)), axis=1)
    retained = np.linalg.norm(weights @ marks)**2
    differences = np.sum(abs(marks[:, None, :]-marks[None, :, :])**2, axis=2)
    fluctuation = .5*(weights @ differences @ weights)
    assert abs(retained+fluctuation-1)<2e-14
    # Exact isotropic fourth moments in nine dimensions, including complex T.
    eye = np.eye(9)
    fourth = (np.einsum("ij,kl->ijkl", eye, eye)+np.einsum("ik,jl->ijkl", eye, eye)+
              np.einsum("il,jk->ijkl", eye, eye))/99
    circular = np.array([1, 1j]+[0]*7)/math.sqrt(2)
    tensor = np.outer(circular, circular)
    polarization_mass = (99/2)*np.einsum("ij,kl,ijkl", tensor.conj(), tensor, fourth)
    assert abs(polarization_mass-1) < 1e-14
    # Same uniform marginal profile. The relative offset changes the matrix force.
    radius, impact = 1., 2.
    images = 2*math.pi*np.arange(-60, 61)
    def interaction(offset):
        return float(np.sum((impact**2+(offset+images)**2)**(-3.5)))
    separations = [math.pi/2, math.pi]
    forces = [interaction(delta) for delta in separations]
    assert forces[0]>forces[1]
    return dict(angular_refinements=refinements, bin_limit=square_mass,
                first_time_overlap=overlap, recovered_active=active, dark_weight=birth_weights[2],
                variance_retained=retained, variance_loss=fluctuation,
                quadrupole_frame=float(polarization_mass.real), paired_kernel=forces)


def continuous_separation():
    # Use the actual normalized Gaussian measure on the integrated innovation,
    # then compare the selected Born weights with the initial measure.
    from scipy.special import roots_hermitenorm, ndtr
    nodes, quadrature = roots_hermitenorm(80)
    quadrature /= math.sqrt(2*math.pi)
    exposure = .75
    # Gauss-Legendre represents a continuous Born distribution on [-1,1].
    spectrum, weights = np.polynomial.legendre.leggauss(36)
    weights = weights*(1+.45*spectrum)/2
    amplitudes = np.exp(np.outer(nodes*math.sqrt(exposure), spectrum) - exposure*spectrum**2)
    likelihood = amplitudes**2 * weights
    mass = likelihood.sum(axis=1)
    post = likelihood/mass[:, None]
    recovered = (quadrature*mass) @ post
    expected = np.exp(-.5*exposure*(spectrum[:, None]-spectrum[None, :])**2)
    actual = amplitudes.T @ (quadrature[:, None]*amplitudes)
    assert np.max(abs(recovered-weights)) < 2e-14 and np.max(abs(actual-expected)) < 2e-14
    cross = float(expected[0, -1])
    error = float(ndtr(-abs(spectrum[0]-spectrum[-1])*math.sqrt(exposure)))
    assert abs(error-.5*math.erfc(math.sqrt(-math.log(cross)))) < 2e-15
    # The action accumulates at the interaction, before a delayed absorber responds.
    time = np.array([0., 1., 2., 3., 4.])
    near, far = np.maximum(time-1, 0), np.maximum(time-3, 0)
    assert all(near >= far) and far[2] == 0 < near[2]
    # Unequal local absorption weights and a genuine material reset.
    probabilities = np.array([.6, .4])*np.array([.35, .8])
    none = 1-probabilities.sum()
    assert abs(sum(probabilities)+none-1)<1e-15
    up, down = .19, .47
    occupancy = up/(up+down)
    assert abs(up*(1-occupancy)-down*occupancy)<1e-15
    return dict(born_recovery_residual=float(max(abs(recovered-weights))),
                gaussian_overlap_residual=float(np.max(abs(actual-expected))),
                endpoint_overlap=cross, equal_prior_error=error, source_exposure=near.tolist(),
                receiver_exposure=far.tolist(), exclusive_absorptions=probabilities.tolist(),
                no_absorption=none, stationary_occupation=occupancy)


def circle_selection():
    impact, speed, source = 3., .6, 1.
    displaced = 1.5
    def phase(radius, coordinate, reference):
        images = 2*math.pi*radius*np.arange(-50, 51)
        return float(speed**3*np.sum((impact**2+(coordinate-reference+images)**2)**(-3)))
    rows = []
    for radius in (2., 5., 20.):
        middle = [math.sin(phase(radius, y, 0)) for y in (source, -source)]
        offset = [math.sin(phase(radius, y, displaced)) for y in (source, -source)]
        assert abs(middle[0]-middle[1]) < 2e-18
        rows.append(dict(radius=radius, centered_rate=(middle[0]-middle[1])**2/2,
                         displaced_rate=(offset[0]-offset[1])**2/2))
    opened = [math.sin(speed**3/(impact**2+(y-displaced)**2)**3) for y in (source,-source)]
    limit = (opened[0]-opened[1])**2/2
    assert limit > 0 and abs(rows[-1]["displaced_rate"]/limit-1) < 1e-10
    return dict(scalar_impact=impact, scalar_speed=speed, source=source, reference=displaced,
                finite_circle=rows, opened_rate=limit)


def recoil_balance():
    # For an angular Fourier shift the opposite momentum goes to the material
    # reference. Work in units where hbar = 1, and test a nonzero incoming momentum.
    mass, radius, incoming = 1.7, 2.3, .35
    harmonics = np.arange(-8, 9)
    # Hermitian multiplication by cos(q/R) + .4 cos(2q/R) on the two-body relative line.
    amplitudes = np.zeros(len(harmonics))
    for order, amplitude in ((1,.5), (2,.2)):
        amplitudes[abs(harmonics)==order] = amplitude
    shifts = harmonics/radius
    energies = ((incoming+shifts)**2-incoming**2)/(2*mass)
    deposited = float(np.dot(amplitudes**2, energies))
    density = lambda q: (-math.sin(q/radius)-.8*math.sin(2*q/radius))**2/(2*mass*radius**2)
    full = quad(density, 0, 2*math.pi*radius)[0]/(2*math.pi*radius)
    assert abs(deposited-full)<1e-14
    left, right = -.3, 1.8
    response = lambda q: math.cos(q/radius)+.4*math.cos(2*q/radius)
    speed = (response(right)-response(left))**2/2
    average = quad(density,left,right)[0]/(right-left)
    lower = speed/(mass*(right-left)**2)
    assert average >= lower > 0
    return dict(kinetic_power_by_recoil=deposited, kinetic_power_by_local_derivative=full,
                arc_power=average, arc_lower_bound=lower)


def helicity_checks():
    # Exterior-algebra lift of the one-mode rotation; columns are |cm,rel>.
    rotation = np.array([[1, 0, 0, 0], [0, -1/math.sqrt(2), 1/math.sqrt(2), 0],
                         [0, 1/math.sqrt(2), 1/math.sqrt(2), 0], [0, 0, 0, -1]])
    assert np.allclose(rotation.T @ rotation, np.eye(4))
    marginals = []
    for relative in (0, 1):
        density = np.diag([.5 if column % 2 == relative else 0 for column in range(4)])
        outgoing = rotation @ density @ rotation.T
        marginals.append(np.trace(outgoing.reshape(2, 2, 2, 2), axis1=1, axis2=3))
    outcomes = np.zeros((2, 9))
    for pattern in product((0, 1), repeat=8):
        for sign, marginal in enumerate(marginals):
            outcomes[sign, sum(pattern)] += math.prod(marginal[n, n] for n in pattern)
    assert np.allclose(outcomes.sum(axis=1), 1) and np.min(outcomes) > 0
    counts = [[Fraction(math.comb(8, m)*3**(m if s else 8-m), 4**8)
               for m in range(9)] for s in (0, 1)]
    assert np.allclose(np.array(counts, dtype=float), outcomes)
    success = sum(max(p, q) for p, q in zip(*counts))/2
    right, wrong = counts[1][-1], counts[1][0]
    return dict(one_mode_occupation=[float(x[1, 1]) for x in marginals],
                occupation_weights=[[float(v) for v in row] for row in counts],
                all_occupations_success=str(success), all_occupations_decimal=float(success),
                matched_port=str(right), wrong_port=str(wrong),
                correct_given_port=str(right/(right+wrong)))


def plot(core, reads):
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.35, 3.14), layout="constrained")
    for row, marker in zip(core, ("o", "s", "^")):
        points = row["samples"]
        left.loglog([s["ka"] for s in points], [abs(s["fractional_change"]) for s in points],
                    marker=marker, label=rf"$\ell={row['ell']}$")
    left.set(xlabel=r"Relative momentum times core radius $ka$",
             ylabel="Fractional change of amplitude")
    left.set_xticks([.125, .25, .5], labels=["0.125", "0.25", "0.5"])
    left.tick_params(axis="x", which="minor", labelbottom=False)
    left.legend(frameon=False, fontsize=8)
    for row, offset, label, color in zip(reads["occupation_weights"], (-.19, .19),
                                         ("Relative helicity −2", "Relative helicity +2"),
                                         ("#24577b", "#ae5429")):
        right.bar(np.arange(9)+offset, row, width=.38, label=label, color=color)
    right.set(xlabel="Occupied fermion modes on one outgoing block", ylabel="Probability",
              xticks=range(9))
    right.legend(frameon=False, fontsize=8)
    (ROOT/"manuscripts").mkdir(exist_ok=True)
    fig.savefig(ROOT/"manuscripts/bound_graviton_breakup.pdf", metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


if __name__ == "__main__":
    result = dict(angular=angular_checks(), exterior_core=hard_core_checks(),
                  spectral=spectral_checks(), superspin=superspin_checks(), encounter=encounter_instrument(), continuum=continuous_layers(), separation=continuous_separation(), circle_layers=circle_selection(), recoil=recoil_balance(), reception=helicity_checks())
    output = ROOT/"verification"
    output.mkdir(exist_ok=True)
    (output/"bound-graviton-breakup-results.json").write_text(
        json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
    plot(result["exterior_core"], result["reception"])
    print("Verified the position-space transform, exterior scattering, source work and helicity marginals.")
