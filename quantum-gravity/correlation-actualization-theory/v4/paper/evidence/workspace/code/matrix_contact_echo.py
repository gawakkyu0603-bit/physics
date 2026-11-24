"""Matrix contact and tidal work in a four-dimensional matrix wave.

The two Fock cutoffs approximate the inclined membranes only. The receiver
uses continuous-time equations for the exact quadratic moments, with frequency
and reduced mass set to one. No random drawing or fitted write rate is used.
"""
import math

import matplotlib.pyplot as plt
import numpy as np
from scipy import sparse
from scipy.integrate import quad, solve_ivp
from scipy.sparse.linalg import eigsh


def contact_spectrum(alpha, beta, size):
    """Diagonalize the actual link Laplacian in a product Hermite basis."""
    lower = sparse.diags(np.sqrt(np.arange(1, size)), 1, format="csr")
    position = (lower + lower.T) / math.sqrt(2)
    momentum_i = (lower - lower.T) / math.sqrt(2)  # i times physical momentum
    identity = sparse.eye(size)
    energy = sparse.diags(2 * np.arange(size) + 1, dtype=float)
    laplacian = (sparse.kronsum(energy, energy)
                 - 2 * math.cos(alpha) * sparse.kron(position, position)
                 - 2 * math.cos(beta) * sparse.kron(momentum_i, momentum_i))
    start = np.sin(np.arange(1, size**2 + 1))
    values, vectors = eigsh(laplacian.tocsr(), k=1, which="SA", v0=start, tol=2e-13)
    ground = vectors[:, 0]
    delta = sparse.kron(position, identity) - sparse.kron(identity, position)
    midpoint = (sparse.kron(momentum_i, identity) - sparse.kron(identity, momentum_i)) / 2
    weights = np.linalg.svd(ground.reshape(size, size), compute_uv=False)**2
    return dict(cutoff=size, gap=float(values[0]), delta_x=float(np.linalg.norm(delta @ ground)**2),
                midpoint_p=float(np.linalg.norm(midpoint @ ground)**2), purity=float(weights @ weights))


def contact_checks():
    alpha, beta = .86, 1.1
    sa, sb = math.sin(alpha / 2), math.sin(beta / 2)
    ca, cb = math.cos(alpha / 2), math.cos(beta / 2)
    f, g = 2 * sa * cb, 2 * ca * sb
    schmidt_scale = math.sqrt(ca * cb / (sa * sb))
    expected = dict(gap=f + g, delta_x=sb / ca, midpoint_p=ca / (4 * sb),
                    purity=2 / (schmidt_scale + 1 / schmidt_scale))
    cutoffs = [contact_spectrum(alpha, beta, size) for size in (8, 14, 22)]
    assert max(abs(cutoffs[-1][key] - value) for key, value in expected.items()) < 2e-9

    # A normalized Gaussian for the link mismatch, integrated independently.
    leakage = []
    for scaled_k in (.1, .5, 1., 2.):
        integral = quad(lambda y: 6 * math.sin(scaled_k*y/2)**4 * math.exp(-y*y/2)
                        / math.sqrt(2*math.pi), -11, 11, epsabs=1e-14)[0]
        t = scaled_k**2
        formula = .75 * (3 - 4*math.exp(-t/2) + math.exp(-2*t))
        assert abs(integral - formula) < 3e-13
        leakage.append([scaled_k, integral])

    # Variable z=d^2 s controls the exponential tail even for large d.
    def potential(distance):
        def integrand(z):
            s = z/distance**2
            diff = 2 * math.sinh(s*(f+g)/2) * math.sinh(s*(f-g)/2)
            return (-math.exp(-z)*diff**2 / (math.sinh(s*f)*math.sinh(s*g))
                    / (z*math.sqrt(4*math.pi*s)))
        return quad(integrand, 0, 65, epsabs=2e-16, epsrel=1e-10)[0]
    leading = -(f*f-g*g)**2 / (16*f*g)
    ratios = [potential(d)*d**3/leading for d in (2., 4., 8.)]
    assert abs(ratios[-1]-1) < 1e-4
    return dict(angles=[alpha, beta], analytic=expected, cutoffs=cutoffs,
                averaged_quartic=leakage, large_distance_ratios=ratios)


PULSE_WIDTH = 3.6
HARMONICS = 2 * np.pi / PULSE_WIDTH * np.arange(1, 5)
COEFFICIENTS = np.array([-56., 28., -8., 1.]) / 128


def curvatures(time, amplitude):
    """Return Kx, Kz and their affine derivatives for h=a sin^8(pi U/L)."""
    phase = HARMONICS * time
    first = -amplitude * np.dot(COEFFICIENTS * HARMONICS, np.sin(phase))
    second = -amplitude * np.dot(COEFFICIENTS * HARMONICS**2, np.cos(phase))
    third = amplitude * np.dot(COEFFICIENTS * HARMONICS**3, np.sin(phase))
    tidal = np.array([second, -second]) - first**2
    slope = np.array([third, -third]) - 2 * first * second
    return tidal, slope, np.array([second**2, first**4])


def evolve(rhs, duration, initial):
    if duration == 0:
        return initial.copy()
    result = solve_ivp(rhs, (0., duration), initial, method="DOP853",
                       atol=3e-14, rtol=2e-12, max_step=duration/32)
    if not result.success:
        raise RuntimeError(result.message)
    return result.y[:, -1]


def transfer(amplitude):
    def rhs(time, state):
        tidal, _, _ = curvatures(time, amplitude)
        matrices = state.reshape(2, 2, 2)
        result = np.empty_like(matrices)
        result[:, 0] = matrices[:, 1]
        result[:, 1] = -(1 + tidal[:, None]) * matrices[:, 0]
        return result.ravel()
    return evolve(rhs, PULSE_WIDTH, np.tile(np.eye(2), (2, 1, 1)).ravel()).reshape(2, 2, 2)


def coefficients(matrices):
    a, b, c, d = (matrices[:, i, j] for i, j in ((0, 0), (0, 1), (1, 0), (1, 1)))
    return (a+d+1j*(c-b))/2, (a-d+1j*(c+b))/2


def echo_moments(amplitude, gap, strength, channel):
    """Solve the full unconditioned covariance and integrate the work separately.

    For zero strength the two extra integrals are the coefficients of the
    first-order vacuum-return deficits for shear and trace monitoring.
    """
    state = np.array([.5, 0., .5, .5, 0., .5, 0., 0., 0.])
    def segment(duration, flat, initial):
        def rhs(time, vector):
            if flat:
                tidal, slope, rates = np.zeros(2), np.zeros(2), np.zeros(2)
            else:
                tidal, slope, rates = curvatures(time, amplitude)
            a = 1 + tidal
            x, xp, p = vector[:6].reshape(2, 3).T
            drift = np.array([2*xp, p-a*x, -2*a*xp])
            second = np.array([2*(p-a*x), -4*a*xp, -2*a*(p-a*x)])
            covariance = drift + strength*rates[channel]*second/2
            # This variance expression uses purity; it is read only at strength=0.
            variance = (.5*(a*x-p)**2+2*a*xp**2).sum()
            return np.r_[covariance.T.ravel(), slope @ x/2, rates*variance]
        return evolve(rhs, duration, initial)
    for duration, flat in ((PULSE_WIDTH, False), (gap, True), (PULSE_WIDTH, False)):
        state = segment(duration, flat, state)
    extra_energy = state[[0, 2, 3, 5]].sum()/2 - 1
    assert abs(extra_energy - state[6]) < 1e-11
    return extra_energy, state[6], state[7:].tolist()


def wave_checks():
    # An exact two-block shifted Gaussian tests the Moyal displacement and sign.
    phase_checks = []
    for delay, shift, sign in ((-.8, .4, 1), (.3, 0., 1), (0., 0., -1)):
        integrand = lambda u: (math.exp(-(u+shift)**2/2)
                               - sign*math.exp(-(u-shift-delay)**2/2))**2
        integral = quad(integrand, -13, 13, epsabs=1e-13)[0]
        analytic = 2*math.sqrt(math.pi) * (1-sign*math.exp(-(2*shift+delay)**2/4))
        assert abs(integral - analytic) < 5e-13
        phase_checks.append([delay, shift, sign, integral])

    rows = []
    for amplitude in (.01, .02, .04, .08):
        matrices = transfer(amplitude)
        alpha, beta = coefficients(matrices)
        defect = max(abs(alpha[0]-alpha[1]), abs(beta[0]+beta[1]),
                     max(abs(np.linalg.det(matrices)-1)))
        assert defect < 2e-11
        gap = (np.angle(alpha[0])-np.pi/2) % np.pi
        rotation = np.array([[math.cos(gap), math.sin(gap)], [-math.sin(gap), math.cos(gap)]])
        _, final_beta = coefficients(matrices @ rotation @ matrices)
        assert max(abs(final_beta)) < 3e-11
        n = abs(beta[0])**2
        lam = n/(1+n)
        marked_return = (1-lam)**2*sum(lam**(2*j) for j in range(60))
        assert abs(marked_return - 1/(1+2*n)) < 8e-14
        coherent, _, coeff = echo_moments(amplitude, gap, 0., 0)
        assert abs(coherent) < 1e-11 and min(coeff) > 0
        strengths = (.3, .3)
        works = [echo_moments(amplitude, gap, value, channel)[0]
                 for channel, value in enumerate(strengths)]
        rows.append(dict(amplitude=amplitude, gap=gap, mean_one_mode=n,
                         partner_residual=float(defect), vacuum_after_single_mark=marked_return,
                         work_after_single_mark=4*n*(1+n), loss_per_unit_G=coeff,
                         work_for_G_point_three=works))
    powers = np.log2(np.array(rows[1]["loss_per_unit_G"])/rows[0]["loss_per_unit_G"])
    assert max(abs(powers-np.array([4, 6]))) < .06
    # A Ricci-flat sandwich, chosen to give full and quarter periods in x,z.
    kappa = .6
    freqs = np.sqrt([1+kappa, 1-kappa])
    angles = np.pi * freqs / freqs[0]
    matrices = np.array([[[np.cos(t), np.sin(t)/w], [-w*np.sin(t), np.cos(t)]]
                         for t, w in zip(angles, freqs)])
    _, beta = coefficients(matrices)
    n_z = abs(beta[1])**2
    scalar_pair = n_z / (4 * (1+n_z)**1.5)
    assert abs(n_z-9/40) < 3e-15 and abs(scalar_pair-9*math.sqrt(10)/686) < 2e-15
    return dict(phase_integrals=phase_checks, pulses=rows, weak_field_powers=powers.tolist(),
                ricci_flat_trace_pair=scalar_pair)


def quantized_exchange():
    """Cavity-normalized resonant pair, with the energy of free recoil included."""
    from scipy.linalg import eigh, expm
    sigma_x = np.array([[0., 1.], [1., 0.]])
    sigma_z = np.diag([1., -1.])
    identity = np.eye(2)
    gap, mass, g = 2., 21., .17
    recoil_frequency = gap + gap**2/(2*mass)
    final_energy = math.hypot(mass+gap, recoil_frequency)
    assert abs(mass+recoil_frequency-final_energy) < 4e-14
    rows = []
    v = g*sigma_x
    initial = np.array([[1., 0.], [0., 0.]])
    for detuning in (0., g, 2*g, 4*g):
        ham = v + detuning*sigma_z/2
        values, unitary = eigh(ham)
        write = unitary @ np.diag(np.diag(unitary.T @ v @ unitary)) @ unitary.T
        k = (values[1]-values[0])/2
        assert np.linalg.norm(write - g*g*ham/k**2) < 2e-15
        comm = lambda op: np.kron(identity, op)-np.kron(op.T, identity)
        generator = -1j*comm(ham)-comm(write) @ comm(write)/2
        time = np.pi/(2*k)
        outgoing = (expm(generator*time) @ initial.ravel(order="F")).reshape(2, 2, order="F")
        rate = 2*g**4/k**2
        fraction = g*g/(2*k*k)*(1-math.exp(-time*rate)*math.cos(2*k*time))
        assert abs(outgoing[1, 1]-fraction) < 2e-14
        assert abs(np.trace(ham @ (outgoing-initial))) < 2e-14
        rows.append(dict(detuning=detuning, rate=rate, conversion=fraction))
    return dict(internal_gap=gap, total_rest_mass=mass, resonant_frequency=recoil_frequency,
                rows=rows)


def continuum_selection():
    """Energy-normalized continua. Compare normalized kernel norms and exact two-pass probabilities."""
    from scipy.special import sici
    norms = []
    for time in (4., 16., 64., 256.):
        result = quad(lambda z: 2*(1-z)*np.sinc(time*z/(2*np.pi))**2, 0, 1,
                      limit=300, epsabs=1e-12)[0]
        si, ci = sici(time)
        analytic = 4*(time*si + math.cos(time)-1 - np.euler_gamma-math.log(time)+ci)/time**2
        assert abs(analytic-result) < 2e-14
        norms.append([time, result, time*result])
    packet_width = .5
    gauss = lambda e: math.exp(-.5*(e/packet_width)**2)/(math.sqrt(2*np.pi)*packet_width)
    rows = []
    for ratio in (.1, 1., 4.):
        widths = np.array([ratio, 1.])
        vector = np.sqrt(widths)
        peak = 4*ratio/(1+ratio)**2
        def residual(detuning):
            scatter = np.eye(2)-1j*np.outer(vector, vector)/(detuning+.5j*widths.sum())
            assert np.linalg.norm(scatter.conj().T @ scatter-np.eye(2)) < 2e-15
            populations = np.abs(scatter[:, 0])**2
            outgoing = scatter.conj().T @ np.diag(populations) @ scatter
            assert abs(outgoing[1, 1]-2*populations.prod()) < 2e-15
            return float(outgoing[1, 1].real)
        value = quad(lambda e: gauss(e)*residual(e), -5, 5, epsabs=5e-13)[0]
        peak_position = widths.sum()/2*math.sqrt(max(0, 2*peak-1))
        expected = .5 if peak >= .5 else 2*peak*(1-peak)
        assert abs(residual(peak_position)-expected) < 2e-15
        rows.append(dict(width_ratio=ratio, line_conversion=peak,
                         detuning_of_maximum=peak_position, max_echo_loss=expected,
                         gaussian_packet_loss=value))
    return dict(kernel_norms=norms, two_channels=rows)


def private_receiver():
    """Compare a local content observable on two noncommuting conditional states."""
    states = np.array([[[.7, .2j], [-.2j, .3]], [[.2, .1], [.1, .8]]])
    observable = np.array([[1., 1j], [-1j, -1.]])
    means = np.trace(states @ observable, axis1=1, axis2=2).real
    squares = np.trace(states @ observable @ observable, axis1=1, axis2=2).real
    within = np.mean(squares-means**2)
    results = []
    for detuning in (1/6, 1.5):
        q = 1/(1+4*detuning**2)
        joint = .5*np.array([[1., 1-q], [0., q]])
        average = 0.
        for weights in joint:
            prob = weights.sum()
            state = np.einsum("i,ijk->jk", weights/prob, states)
            moment = np.trace(state @ observable).real
            average += prob*(np.trace(state @ observable @ observable).real-moment**2)
        coefficient = .25*(1-q)/(1-.5*q)
        assert abs(average-within-coefficient*(means[1]-means[0])**2) < 1e-14
        results.append(dict(line_detuning=detuning, capture=q, between_fraction=coefficient,
                            mean_quantum_variance=average))
    return dict(conditional=results, internal_variance=within)


def local_flux():
    """A resonant continuum conversion with the same spectrum before/after a causal phase shift."""
    ga, gb = .7, 1.3
    width = ga+gb
    kappa = width/2
    def incoming(t):
        return 2*kappa**1.5*t*math.exp(-kappa*t)
    def rhs(t, y):
        c, reference, first, second, moment_first, moment_second = y
        b = -math.sqrt(gb)*c
        filtered = b-math.sqrt(2*kappa)*reference
        return [-kappa*c+math.sqrt(ga)*incoming(t), -kappa*reference+math.sqrt(2*kappa)*b,
                b*b, filtered*filtered, t*b*b, t*filtered*filtered]
    result = solve_ivp(rhs, (0, 47/kappa), np.zeros(6), method="DOP853",
                       atol=3e-14, rtol=2e-12, max_step=.15/kappa, dense_output=True)
    if not result.success:
        raise RuntimeError(result.message)
    c, reference, norm, filtered_norm, first, second = result.y[:, -1]
    expected_norm = 3*ga*gb/width**2
    assert abs(norm-expected_norm) < 2e-12 and abs(filtered_norm-norm) < 2e-12
    assert abs(first/norm*width-5) < 2e-10 and abs(second/filtered_norm*width-25/3) < 2e-10
    cross = result.sol(3/width)
    null_flux = (-math.sqrt(gb)*cross[0]-math.sqrt(2*kappa)*cross[1])**2
    # The scattering amplitudes are those of a local junction; check also
    # their energy-resolved group delay with the transmitted wave packet.
    spectral = lambda z: 1/(z*z+kappa*kappa)**3
    weight = quad(spectral, -np.inf, np.inf, epsabs=2e-13)[0]
    delay = quad(lambda z: spectral(z)*2*kappa/(z*z+kappa*kappa),
                 -np.inf, np.inf, epsabs=2e-13)[0]/weight
    assert null_flux < 1e-22 and abs(delay-(second/filtered_norm-first/norm)) < 2e-12
    clocks = [quad(lambda x: math.exp(-x)*x**4/24*(1-x/3)**(2*j)*(1-math.cos(x))/2,
                   0, 95, epsabs=1e-13)[0] for j in (0, 1)]
    assert max(abs(clocks[0]-9/16), abs(clocks[1]-11/24)) < 2e-14
    return dict(partial_widths=[ga, gb], total_conversion=norm, filtered_conversion=filtered_norm,
                conditional_clock_excitation=clocks,
                dimensionless_means=[width*first/norm, width*second/filtered_norm],
                flux_at_delayed_node=null_flux, delay_from_scattering_phase=delay)


def matrix_contact_checks():
    return dict(membranes=contact_checks(), receiver=wave_checks(), dressed_pair=quantized_exchange(),
                continuum=continuum_selection(), private=private_receiver(), local_flux=local_flux())


def draw_contact(root, data):
    figure, axes = plt.subplots(1, 2, figsize=(8.5, 3.25), layout="constrained")
    xs = np.logspace(-1.3, .5, 100)
    loss = .75*(3 - 4*np.exp(-xs**2/2) + np.exp(-2*xs**2))
    axes[0].loglog(xs, loss, color="#275272", label="Matrix contact")
    axes[0].loglog(xs[xs < .6], 9*xs[xs < .6]**4/8, "--", color="#a55826", label="Long wavelengths")
    axes[0].set(xlabel=r"Wave number times registration width $k\sigma$",
                ylabel="Mean fourth power of tidal difference", title="The same wave seen at two endpoints")
    rows = data["receiver"]["pulses"]
    for mode, (label, color) in enumerate((("Shear", "#275272"), ("Trace", "#a55826"))):
        axes[1].loglog([r["amplitude"] for r in rows],
                       [r["loss_per_unit_G"][mode] for r in rows], "o-", ms=4,
                       label=label, color=color)
    axes[1].set(xlabel=r"Amplitude of the matrix wave $h$", ylabel="Vacuum loss per unit coupling",
                title="A material receiver after a coherent echo")
    for axis in axes:
        axis.legend(frameon=False, fontsize=8)
        axis.spines[["top", "right"]].set_visible(False)
    figure.savefig(root/"manuscripts/matrix_contact_echo.pdf",
                   metadata={"CreationDate": None, "ModDate": None})
    plt.close(figure)
