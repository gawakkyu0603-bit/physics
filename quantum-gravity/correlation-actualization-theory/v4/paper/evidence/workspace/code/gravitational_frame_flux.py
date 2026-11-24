"""Transport of a quadrupole direction, its energy cost, and the receiving horizon.

All frequencies in the absorption calculation use Schwarzschild time at infinity.
The shared transmission solver uses M=1, hence omega=(r_h*omega)/2 there.
"""
import math
from fractions import Fraction

import numpy as np
from numpy.polynomial.legendre import leggauss, legvander
from scipy.integrate import quad
from scipy.linalg import eigh, expm
from scipy.special import eval_legendre

from hawking_absorption_records import transmission


def alignment_bound(visibility):
    return 9*visibility**2/(2*(1-visibility)*(1+2*visibility))


def transport_checks():
    grav, inner, outer = .7, 2.7, 8.1
    radial, _ = quad(lambda r: 6*grav/r**4, inner, outer)
    inverse_inertia = 2*grav*(inner**-3-outer**-3)
    np.testing.assert_allclose(radial, inverse_inertia)
    mass = inner/(2*grav)
    np.testing.assert_allclose(1/(2*grav*inner**-3), 4*grav**2*mass**3)
    impulse, alpha = .67, .38
    x, weight = leggauss(180)
    weight /= 2
    spins = np.arange(0, 50, 2)
    casimir = spins*(spins+1)
    basis = legvander(x, spins[-1])[:, spins]*np.sqrt(2*spins+1)
    p2 = (3*x*x-1)/2
    alignment = basis.T @ ((weight*p2)[:, None]*basis)
    examples = []
    for centered in (False, True):
        potential = p2**2-2*int(centered)*p2
        contact = basis.T @ ((weight*potential)[:, None]*basis)
        assert np.min(np.diag(contact, k=2)) > .01 and abs(contact[0, 1]) > .1
        amplitude = basis.T @ (weight*np.exp(-1j*impulse*potential))
        np.testing.assert_allclose(np.linalg.norm(amplitude), 1, atol=2e-14)
        recoil = np.dot(casimir, abs(amplitude)**2)
        coefficient = Fraction(144 if centered else 24, 35)
        np.testing.assert_allclose(recoil, float(coefficient)*impulse**2, rtol=2e-12)
        rate = (1j*alpha*np.vdot(amplitude, (casimir[:, None]-casimir[None, :])*alignment @ amplitude)).real
        prediction = alpha*impulse*(144 if centered else -24)/35
        np.testing.assert_allclose(rate, prediction, atol=4e-13)
        np.testing.assert_allclose(np.vdot(amplitude, alignment @ amplitude), 0, atol=4e-13)
        # Negative and positive energy drift witness a failure of all-state conservation.
        total_hamiltonian = np.diag(alpha*casimir) + contact
        read_value = casimir/max(casimir)
        drift = -.5*(read_value[:, None]-read_value[None, :])**2*total_hamiltonian
        energy_drift = np.linalg.eigvalsh(drift)
        assert energy_drift[0] < -1e-4 and energy_drift[-1] > 1e-4
        examples.append(dict(centered=centered, angular_work=float(recoil),
                             initial_alignment_slope=float(rate),
                             energy_drift_extrema=energy_drift[[0, -1]].tolist()))
    return dict(radial_inverse_inertia=inverse_inertia, horizon_inertia=4*grav**2*mass**3,
                impulse=impulse, alpha=alpha, response=examples)


def localization_checks():
    # Normalized angular measure for two unoriented axes is dx on 0 < x < 1.
    x, w = leggauss(240)
    x, w = (1+x)/2, w/2
    p2 = (3*x*x-1)/2
    packets = []
    for concentration in (1., 5., 20., 80., 320., 1000.):
        probability = w*np.exp(concentration*(x*x-1))
        probability /= probability.sum()
        visibility = np.dot(probability, p2)
        axial_variance = np.dot(probability, x*x*(1-x*x))
        angular_work = concentration**2*axial_variance
        lower = alignment_bound(visibility)
        np.testing.assert_allclose(angular_work, concentration*visibility, rtol=2e-10)
        assert angular_work >= lower
        packets.append(dict(concentration=concentration, visibility=float(visibility),
                            casimir=float(angular_work), lower=float(lower),
                            scaled_cost=float((1-visibility)*angular_work)))
    assert abs(packets[-1]["scaled_cost"]-1.5) < .003
    # Variational comparison, diagonalizing J^2-lambda*P2 in an even rotor basis.
    variational = []
    for coupling in (2, 10, 40, 160, 640, 2560):
        solutions = []
        for blocks in (24, 34):
            j = 2*np.arange(blocks)
            basis = legvander(x, j[-1])[:, j]*np.sqrt(2*j+1)
            alignment = basis.T @ ((w*p2)[:, None]*basis)
            energies, eig = eigh(np.diag(j*(j+1))-coupling*alignment,
                                 subset_by_index=(0, 0))
            state = eig[:, 0]
            v = state @ alignment @ state
            q = np.dot(j*(j+1), state**2)
            assert q >= alignment_bound(v)-1e-9
            solutions.append([v, q, energies[0]])
        np.testing.assert_allclose(*solutions, rtol=1e-9, atol=5e-9)
        variational.append(dict(coupling=coupling, visibility=float(v), casimir=float(q)))
    return dict(packets=packets, variational=variational)


def line_strength(initial, final, ell):
    """Mass STF contraction and magnetic sum from the axial integral."""
    def integrand(x):
        return eval_legendre(initial, x)*eval_legendre(ell, x)*eval_legendre(final, x)
    angular, _ = quad(integrand, -1, 1, epsabs=1e-13)
    double_factorial = math.prod(range(1, 2*ell, 2))
    return math.factorial(ell)/double_factorial*(2*final+1)*angular/2


def line_checks():
    strengths = [line_strength(2, 0, 2), line_strength(4, 2, 2), line_strength(4, 0, 4)]
    np.testing.assert_allclose(strengths, [2/15, 4/21, 8/315], rtol=1e-13)
    decay_ratio = strengths[1]/strengths[0]*(7/3)**5
    np.testing.assert_allclose(decay_ratio, 24010/243)
    def luminosity(ell):
        double_factorial = math.prod(range(1, 2*ell+2, 2))
        return (ell+1)*(ell+2)/((ell-1)*ell*math.factorial(ell)*double_factorial)
    np.testing.assert_allclose(luminosity(4)*strengths[2]/(luminosity(2)*strengths[1]), 1/13608)
    histories = []
    for gamma42, gamma40, gamma20 in ((.7, .3, 1.), (.9, .02, .025)):
        total = gamma42+gamma40
        generator = np.array([[-total, 0, 0], [gamma42, -gamma20, 0],
                              [gamma40, gamma20, 0]])
        p4, p2 = .19, .11
        for time in (.1, 2., 20.):
            surviving = math.exp(-total*time)
            if total == gamma20:
                integral = time*surviving
            else:
                integral = (math.exp(-gamma20*time)-surviving)/(total-gamma20)
            populations = expm(time*generator) @ [p4, p2, 1-p4-p2]
            np.testing.assert_allclose(populations[:2],
                                       [p4*surviving, p2*math.exp(-gamma20*time)+p4*gamma42*integral])
        histories.append(dict(branch=gamma42/total, coincident_widths=total==gamma20))
    # Use both parity potentials and different matching strategies in the existing solver.
    # q_net is proportional to sigma. The KMS gain factor is evaluated stably with expm1.
    spectra = []
    for low in (.003, .012, .04, .09):
        scales = [low, (7/3)*low]
        sigma, errors, top_fractions = [], [], []
        for scale in scales:
            ell = np.arange(2, 7)
            odd = transmission(scale/2, maximum=6)
            even = transmission(scale/2, maximum=6, even=True)
            sigma.append(float(np.dot(2*ell+1, odd)/scale**2))  # in units pi*r_h^2
            errors.append(float(abs(np.dot(2*ell+1, odd-even)/np.dot(2*ell+1, odd))))
            top_fractions.append(float((2*ell[-1]+1)*odd[-1]/np.dot(2*ell+1, odd)))
        assert max(errors) < 5e-7 and max(top_fractions) < 1e-11
        net = sigma[1]/sigma[0]
        gain = net*np.expm1(-4*np.pi*scales[0])/np.expm1(-4*np.pi*scales[1])
        spectra.append(dict(low=low, low_sigma_over_leading=sigma[0]/((4/45)*low**4),
                            net_pair=net, gain_pair=float(gain),
                            parity_error=max(errors), last_mode_fraction=max(top_fractions)))
    assert abs(spectra[0]["net_pair"]/(7/3)**4-1) < .022
    assert abs(spectra[0]["gain_pair"]/(7/3)**3-1) < .055
    return dict(strengths=strengths, width_ratio=decay_ratio, cascades=histories, spectra=spectra)


def angular_channel_checks():
    # Product quadrature integrates the relevant harmonics and their products on the sphere.
    cosine, polar_weight = leggauss(7)
    azimuth = 2*np.pi*np.arange(13)/13
    z, phi = np.meshgrid(cosine, azimuth, indexing="ij")
    radius = np.sqrt(1-z*z)
    directions = np.column_stack(((radius*np.cos(phi)).ravel(), (radius*np.sin(phi)).ravel(), z.ravel()))
    weights = np.repeat(polar_weight/26, 13)
    dot = np.clip(directions @ directions.T, -1, 1)
    tidal = (3*dot**2-1)/2
    channels = []
    for centered in (False, True):
        kernel = tidal**2-2*int(centered)*tidal-.2
        gram = np.sqrt(weights[:, None]*weights[None, :])*kernel
        measured = np.linalg.eigvalsh(gram)
        rank_two = -12/35 if centered else 2/35
        expected = np.r_[np.full(5, rank_two), np.full(9, 2/35), np.zeros(len(gram)-14)]
        np.testing.assert_allclose(measured, np.sort(expected), atol=2e-15)
        channels.append(dict(centered=centered, rank_two=rank_two, rank_four=2/35,
                             positive=int(np.sum(measured>1e-9)), negative=int(np.sum(measured < -1e-9))))
    generators = [np.array([[0,0,0],[0,0,-1],[0,1,0.]]),
                  np.array([[0,-1,0],[1,0,0],[0,0,0.]])]
    tide = np.diag([-1,-1,2])/np.sqrt(6)
    def ordered(angle):
        first, second = [expm(angle*g) for g in generators]
        left, right = first@second, second@first
        return np.linalg.norm(left@tide@left.T-right@tide@right.T)**2
    np.testing.assert_allclose(ordered(np.pi/2), 3)
    np.testing.assert_allclose(ordered(.0005)/(.0005**4), 3, rtol=3e-7)
    # Reversing a three-setting experiment symmetrizes the Gram matrix of the
    # two consecutive source displacements. Let d be each squared length and
    # c their inner product. Positivity then amounts to -d <= c <= d.
    from scipy.optimize import linprog
    optimum = linprog([0, 0, 1], A_ub=[[1,0,-1],[-1,0,-1],[2,2,-16],[-2,-2,-16],
                                      [-1,1,0],[-1,-1,0]],
                      b_ub=[1,-1,16,-16,0,0], bounds=[(0,None),(None,None),(0,None)],
                      method="highs")
    assert optimum.success
    np.testing.assert_allclose(optimum.x, [1.6, 1.6, .6], atol=2e-14)
    ideal_stiffness, contrast_coupling = 1.7, -.4
    settings = np.array([.2, .9, 1.6])
    contrast_squared = (settings[:, None]-settings[None, :])**2
    induced_field = contrast_coupling*contrast_squared/ideal_stiffness
    eliminated = -ideal_stiffness*induced_field**2/2+contrast_coupling*induced_field*contrast_squared
    np.testing.assert_allclose(eliminated, contrast_coupling**2*contrast_squared**2/(2*ideal_stiffness))
    return dict(channels=channels, quarter_turn_norm_squared=float(ordered(np.pi/2)),
                optimum_three_setting_error=float(optimum.fun), optimal_gram=optimum.x[:2].tolist())


def matrix_scattering_checks():
    """One-loop D0 elastic determinant compared with the long-distance action.

    q=|v|/b^2 uses the units of Douglas et al., Eq. (3.3). Probabilities
    use expm1 to retain the rare channels when subtraction from unity fails.
    """
    from scipy.special import loggamma

    def excited(speed):
        return -np.expm1(-16*np.arctanh(np.exp(-np.pi/speed)))

    samples = []
    for q in (.2, .12, .08, .05, .035, .02):
        y = 1/(2*q)
        angle = np.angle((1j+q)/(1j-q)) + 8*(loggamma(.5+1j*y).imag-loggamma(1j*y).imag)
        phase = float(np.angle(np.exp(1j*angle)))
        probability = float(excited(q))
        double_probability = float(excited(2*q))
        u = np.exp(-np.pi/(2*q))
        def reduced(x):
            return 16*(1+7*x**2+7*x**4+x**6)/(1+x)**8
        np.testing.assert_allclose(probability, u**2*reduced(u**2), rtol=4e-14, atol=0)
        ratio = double_probability**2/probability
        np.testing.assert_allclose(ratio, reduced(u)**2/reduced(u*u), rtol=6e-14)
        samples.append(dict(speed_over_b2=q, exact_phase=phase, phase_over_cubic=phase/q**3,
                            excitation=probability, doubled_hit_ratio=ratio,
                            linked_phase=phase*np.log(16/probability)**3))
    assert abs(samples[-1]["phase_over_cubic"]-1) < 4e-7
    assert abs(samples[-1]["linked_phase"]-np.pi**3) < 1.1e-5
    windows = []
    for t in (.02, .5, 2., 40.):
        def partial(s):
            z = s/np.hypot(1, s)
            return z-2*z**3/3+z**5/5
        numerical, _ = quad(lambda u: (1+u*u)**(-3.5), 0, t, epsabs=1e-13)
        np.testing.assert_allclose(numerical, partial(t), rtol=2e-14)
        phase_ratio = 8*partial(2*t)/partial(t)
        windows.append(dict(scaled_duration=t, phase_ratio=phase_ratio,
                            least_relative_error=(phase_ratio-4)/(phase_ratio+4)))
    integral, _ = quad(lambda u: (1+u*u)**(-3.5), -np.inf, np.inf)
    np.testing.assert_allclose(integral*15/16, 1)
    return dict(samples=samples, windows=windows)


def draw_frame_flux(root, results):
    import matplotlib.pyplot as plt
    fig, (cost, receiver) = plt.subplots(1, 2, figsize=(8.5, 3.3), layout="constrained")
    deficit = np.geomspace(.001, .65, 250)
    cost.semilogx(deficit, deficit*alignment_bound(1-deficit), color="#204f68", label="Energy lower bound")
    packets = results["localization"]["packets"]
    cost.plot([1-r["visibility"] for r in packets], [r["scaled_cost"] for r in packets],
              "o", markersize=4, color="#ae582b", label="Prepared angular packet")
    optimal = results["localization"]["variational"]
    cost.plot([1-r["visibility"] for r in optimal], [(1-r["visibility"])*r["casimir"] for r in optimal],
              "+", markersize=6, color="#24372d", label="Minimum at fixed alignment")
    cost.set(xlabel=r"Angular deficit $1-v$", ylabel=r"$(1-v)\langle J^2\rangle$",
             title="Energy needed to match two axes", ylim=(0, 1.62))
    cost.legend(frameon=False, fontsize=8)
    rows = results["lines"]["spectra"]
    for name, label, power, color in [("net_pair", "Net absorption", 4, "#204f68"),
                                      ("gain_pair", "Upward transitions", 3, "#ae582b")]:
        receiver.semilogx([r["low"] for r in rows], [r[name] for r in rows], "o-",
                          color=color, label=label, markersize=4)
        receiver.axhline((7/3)**power, color=color, ls=":", lw=.9)
    receiver.set(xlabel=r"Lower line frequency $r_h\omega_{20}$", ylabel="High / low receiver response",
                 title="Two lines incident on a black hole")
    receiver.legend(frameon=False, fontsize=8)
    for axis in (cost, receiver):
        axis.spines[["top", "right"]].set_visible(False)
    fig.savefig(root/"manuscripts/gravitational_frame_flux.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def frame_flux_checks():
    return dict(angular=angular_channel_checks(), transport=transport_checks(), localization=localization_checks(),
                lines=line_checks(), matrix_scattering=matrix_scattering_checks())
