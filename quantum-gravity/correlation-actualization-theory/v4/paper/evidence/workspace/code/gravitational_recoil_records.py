"""Recoil, a closed gravitational response, pair fluctuations and private pulse reads."""
import math

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigvalsh, toeplitz
from scipy.stats import binom, nbinom, poisson


def clock_contrast(x):
    """Difference of the excited populations of the two prepared material clocks."""
    z = 1 / (1 - 1j*x)
    return (5/3 * (z**7-z**6)).real


def check_clock():
    mass, gap = 5., .7
    rows = []
    for rapidity in (-1.2, 0., .7):
        transverse = .32
        u = math.hypot(mass, transverse)*math.exp(-rapidity)
        shift = (2*mass*gap+gap**2)/(2*u)
        plus = (mass**2+transverse**2)/u
        for carrier in (2.1, 7.3):
            if carrier <= shift:
                raise ValueError("Both material sidebands must be open")
            outgoing = carrier-shift
            new_plus = ((mass+gap)**2+transverse**2)/u
            assert abs(new_plus/2+outgoing-(plus/2+carrier)) < 4e-15
            assert abs((new_plus-u)/2+outgoing-((plus-u)/2+carrier)) < 4e-15
        rows.append(dict(rapidity=rapidity, excitation_recoil=shift))
    for x in (.2, .8, 1., 3.):
        integrand = lambda t: math.exp(-t)*t**4/24*(1-(1-t/3)**2)*(1-math.cos(x*t))/2
        numerical = quad(integrand, 0, 80, epsabs=4e-14)[0]
        assert abs(numerical-clock_contrast(x)) < 3e-13
    scales = np.array([.17, .8, 3.9])
    weights = np.array([.15, .55, .30])
    integral = quad(lambda y: weights@clock_contrast(scales*np.exp(y)), -22, 19,
                    epsabs=1e-13, epsrel=2e-13)[0]
    roots = np.tan(np.arange(1, 4)*np.pi/7)
    assert abs(integral+5/18) < 3e-13 and max(abs(clock_contrast(roots))) < 7e-15
    return dict(recoil=rows, scan_area=integral, zero_crossings=roots.tolist())


def check_closed_exchange():
    """Integrate an oscillator driven by four disjoint bumps, including the enclosure phase."""
    # Work in its rotating frame, d alpha /dt = drive; Im(alpha* d alpha) is the phase.
    widths = [.37, .42, .28, .34]
    shifts = [.18, 1.22, 2.2, 3.14]
    alpha, beta = .31+.16j, -.22+.42j
    out = []
    for orientation in (1, -1):
        side_b = orientation*beta
        corners = [alpha, side_b, -alpha, -side_b]
        def derivative(t, state):
            velocity = 0j
            for start, width, step in zip(shifts, widths, corners):
                if start < t < start+width:
                    velocity += step*2*math.sin(math.pi*(t-start)/width)**2/width
            return [velocity, (state[0].conjugate()*velocity).imag]
        result = solve_ivp(derivative, (0, 4), [0j, 0j], method="DOP853",
                           max_step=.018, rtol=1e-11, atol=2e-13)
        if not result.success:
            raise RuntimeError(result.message)
        residual, accumulated = result.y[:, -1]
        expected = 2*(alpha.conjugate()*side_b).imag
        assert abs(residual) < 2e-9 and abs(accumulated-expected) < 2e-9
        out.append(dict(orientation=orientation, displacement=abs(residual),
                        phase=accumulated.real, instantaneous_overlap=0.0))
    # The initial thermal state is arbitrary. For an open path compare the
    # Laguerre-polynomial sum for a thermal characteristic function to its Gaussian.
    from scipy.special import eval_laguerre
    occupation, mismatch = .61, .39
    n = np.arange(75)
    number_weights = (occupation/(1+occupation))**n/(1+occupation)
    overlap = sum(number_weights*np.exp(-mismatch**2/2)*eval_laguerre(n, mismatch**2))
    assert abs(overlap-math.exp(-(occupation+.5)*mismatch**2)) < 1e-14
    return dict(closed=out, open_visibility=float(overlap))


def check_pairs():
    """Integrate one fermionic crossing and one transverse charged oscillator."""
    rows = []
    for impact in (.65, .93):
        endpoint = 27.
        def matrix(t):
            return np.array([[t, impact], [impact, -t]])
        initial = np.linalg.eigh(matrix(-endpoint))[1][:, 0].astype(complex)
        solution = solve_ivp(lambda t, y: -1j*matrix(t)@y, (-endpoint, endpoint), initial,
                             method="DOP853", rtol=8e-11, atol=3e-13)
        positive = np.linalg.eigh(matrix(endpoint))[1][:, 1]
        fermion = abs(positive@solution.y[:, -1])**2
        omega = math.hypot(endpoint, impact)
        amplitude = 1/math.sqrt(2*omega)
        def slope(t):
            return -1j*omega-t/(2*omega**2)
        oscillator = solve_ivp(lambda t, y: [y[1], -(impact**2+t*t)*y[0]],
                               (-endpoint, endpoint), [amplitude+0j, amplitude*slope(-endpoint)],
                               method="DOP853", rtol=8e-11, atol=3e-13)
        if not solution.success or not oscillator.success:
            raise RuntimeError("pair differential equation failed")
        value, velocity = oscillator.y[:, -1]
        boson = abs((velocity-slope(endpoint)*value)/(2j*omega*amplitude))**2
        p = math.exp(-math.pi*impact**2)
        assert abs(fermion-p)<3e-5 and abs(boson-p)<7e-6
        # The eight integer counts of boson pairs sum to a negative binomial.
        fermion_weights = binom.pmf(np.arange(9), 8, p)
        boson_weights = nbinom.pmf(np.arange(110), 8, 1/(1+p))
        total = np.convolve(fermion_weights, boson_weights)
        k = np.arange(len(total))
        mean = total@k
        second = total@(k*(k-1))
        third = total@(k*(k-1)*(k-2))-3*second*mean+2*mean**3
        assert abs(total.sum()-1)<2e-14 and abs(second-mean**2)<4e-13
        assert abs(third/mean**3-1/128)<4e-13
        assert abs(total[0]-math.tanh(math.pi*impact**2/2)**8)<5e-14
        rows.append(dict(impact=impact, asymptotic_pair=p, fermion_ode=fermion,
                         boson_ode=boson, mean=float(mean), vacuum=float(total[0]),
                         normalized_third=float(third/mean**3)))
    return rows


def check_pulse_reads():
    rows = []
    for t in (.06, .3, 1.4):
        r = math.exp(-t)
        symbol_min = (1-r)/(1+r)
        gram = toeplitz(r**np.arange(112))
        finite_min = eigvalsh(gram, subset_by_index=[0, 0])[0]
        assert symbol_min <= finite_min < symbol_min+2e-4
        packet = math.sqrt(1-r*r)*r**np.arange(512)
        success = (packet-r*np.r_[0, packet[:-1]])/(1+r)
        assert max(abs(success[1:]))<3e-16 and abs(success[0]**2-symbol_min)<3e-15
        phases = np.exp(1j*np.linspace(-np.pi, np.pi, 197))
        norm = (abs(1-r*phases)**2+r*abs(1+phases)**2)/(1+r)**2
        assert max(abs(norm-1))<1e-15
        multiplicity = np.arange(90)
        occupation = 2.8
        optimum = float(poisson.pmf(multiplicity, occupation)@np.tanh(t*multiplicity/2))
        local_read = -math.expm1(-occupation*symbol_min)
        assert local_read <= optimum <= min(1, occupation*t/2)
        aliases = (2*np.arange(-160, 160)+1)*np.pi
        three_pole = float((16/3)*t**5*np.sum((t*t+aliases**2)**-3))
        assert three_pole <= t**5/90
        rows.append(dict(damping_times_spacing=t, causal_success=symbol_min,
                         finite_gram_lower_edge=float(finite_min), captured_quanta=occupation,
                         independent_reads=local_read, collective_upper=optimum,
                         third_order_midpoint=three_pole))
    return rows


def check_gravity_echo():
    """First-passage pairs, their received radiation and two intrinsic contact actions."""
    p, received_per_pair_squared, exposure = .19, .13, .74
    weights = np.convolve(binom.pmf(np.arange(9), 8, p),
                          nbinom.pmf(np.arange(90), 8, 1/(1+p)))
    counts = np.arange(len(weights))
    means = received_per_pair_squared*counts**2
    dark = weights@np.exp(-means)
    direct = weights@np.exp(means*math.expm1(-exposure))
    bounded = dark+(1-dark)*math.exp(-exposure)
    # Sum the actual incident occupation probabilities independently for each K.
    averaged = np.zeros(2)
    for weight, mean in zip(weights, means):
        if weight < 2e-18:
            continue
        occupations = np.arange(int(poisson.isf(1e-14, mean))+2)
        probability = poisson.pmf(occupations, mean)
        averaged[0] += weight*(probability@np.exp(-exposure*occupations))
        averaged[1] += weight*(probability@np.exp(-exposure*(occupations>0)))
    assert np.allclose(averaged, [direct, bounded], rtol=0, atol=3e-14)
    assert dark <= direct <= bounded < 1
    assert 1-direct <= received_per_pair_squared*(-math.expm1(-exposure))*((16*p)**2+16*p)
    # A connected matrix phase from offsets on the two blocks, in matrix units.
    b, da, db, speed = 2.3, .18, .32, .45
    phase = lambda radius: abs(speed)**3/radius**6
    rectangle = phase(b+da-db)+phase(b)-phase(b+da)-phase(b-db)
    integrated = -42*abs(speed)**3*quad(
        lambda x: quad(lambda y: (b+x-y)**-8, 0, db)[0], 0, da)[0]
    assert abs(rectangle-integrated)<4e-18
    assert 42*abs(speed)**3*da*db/(b+da)**8 <= abs(rectangle) <= 42*abs(speed)**3*da*db/(b-db)**8
    matched = (1-dark)*(-math.expm1(-2*abs(rectangle)))
    assert 1-bounded >= matched > 0
    return dict(pair_probability=p, captured_occupation_at_one_pair=received_per_pair_squared,
                absolute_contact_exposure=exposure, no_graviton=dark, full_magnitude_recovery=1.,
                signed_count_visibility=direct, bounded_signed_visibility=bounded,
                connected_matrix_phase=rectangle, integrated_matrix_phase=integrated,
                matched_minimum_visibility_loss=matched)


def check_positive_energy():
    """Fold normalized positive-energy spectra onto the phase circle at T=hbar=1."""
    mean_energy = .9
    half_band = math.pi
    rows = []
    for cutoff in (.4, .08, .016):
        floor = (mean_energy-cutoff/2)/(half_band-cutoff/2)
        plateau = floor/(2*math.pi)
        def density(e):
            flat = plateau if 0<=e<=2*math.pi else 0.
            low = (1-floor)/cutoff if 0<=e<cutoff else 0.
            return flat+low
        norm = quad(density, 0, 2*math.pi, points=[cutoff])[0]
        mean = quad(lambda e:e*density(e), 0, 2*math.pi, points=[cutoff])[0]
        folded = 2*math.pi*np.array([density(.5*cutoff), density(1.5*cutoff), density(4.)])
        assert abs(norm-1)<2e-15 and abs(mean-mean_energy)<1e-15
        assert abs(min(folded)-floor)<1e-15 and floor < mean_energy/math.pi
        rows.append(dict(low_bandwidth=cutoff, exact_mean=mean, success=floor))
    assert rows[0]["success"]<rows[1]["success"]<rows[2]["success"]
    return dict(mean_energy_budget=mean_energy/math.pi, approach_to_bound=rows)


def check_infall():
    rows = []
    for f in (.03, .003, .0003, .00003):
        v = math.sqrt(1-f)
        ratio = 3*math.sqrt(3)*(1-f)/2
        c = math.sqrt(1-ratio**2*f)
        # Rationalization retains the tiny comoving solid angle near the horizon.
        escape = ratio**2*f*f/(2*(1+v)*(1+c)*(1+v*c))
        mean_redshift = f/(1+v)+v*escape
        # Integrate on the static sky, using the aberration Jacobian for comoving emission.
        span = ratio**2*f/(1+c)
        number = quad(lambda t: span*f/(2*(1+v*(1-span*t))**2), 0, 1)[0]
        energy = quad(lambda t: span*f**2/(2*(1+v*(1-span*t))**3), 0, 1)[0]
        assert abs(escape-number)<2e-13*escape and abs(escape*mean_redshift-energy)<2e-13*energy
        rows.append(dict(lapse_squared=f, captured_fraction=escape, energy_fraction=energy,
                         scaled_number=escape/f**2, scaled_energy=energy/f**3))
    assert abs(rows[-1]["scaled_number"]-27/64)<3e-5
    assert abs(rows[-1]["scaled_energy"]-27/128)<3e-5
    return rows


def check_supercharges():
    """Sixteen Clifford generators on all 256 polarizations, plus an orbital multiplicity."""
    basis = np.arange(256)
    permutations, phases = [], []
    for bit in range(8):
        lower_parity = np.array([(-1)**(int(i) % (1<<bit)).bit_count() for i in basis])
        local_z = 1-2*((basis>>bit)&1)
        for phase in (lower_parity, 1j*lower_parity*local_z):
            permutations.append(basis^(1<<bit))
            phases.append(phase)
    for i in range(16):
        for j in range(16):
            ij = phases[j]*phases[i][permutations[j]]
            ji = phases[i]*phases[j][permutations[i]]
            assert np.array_equal(permutations[i][permutations[j]], permutations[j][permutations[i]])
            assert np.max(abs(ij+ji-2*(i==j)))==0
    strength = .8
    signed = 1-2*(basis&1)
    kraus = np.sqrt((1+np.outer([strength, -strength], signed))/2)
    paired = permutations[0]
    multiplier = np.sum(kraus*kraus[:, paired], axis=0)
    defect = max(abs(multiplier-1))
    outcomes = np.sum((kraus-kraus[:, paired])**2, axis=0)
    assert np.max(abs(outcomes-2*defect)) < 3e-15
    # A directional charge that acts only on the orbital multiplicity has no spin defect.
    for sign in (-1, 1):
        orbital = np.full(256, math.sqrt((1+strength*sign)/2))
        assert all(np.max(abs(orbital-orbital[permutation]))==0 for permutation in permutations)
    completions = []
    for contact in (-7., .23, 1.6):
        energy = 1.4
        x = contact/energy
        factors = [1+math.tanh(x), 1+x/math.hypot(1, x)]
        for factor in factors:
            assert factor>0 and abs((math.sqrt(factor)*math.sqrt(energy))**2-energy*factor)<1e-14
        completions.append(dict(contact=contact, initial_energy=energy,
                                new_energies=[energy*f for f in factors]))
    # A disconnected spectator must leave the contact energy untouched.
    active_energy, contact = 1.4, 1.6
    spectator_energies = [0., 2., 40., 1.e4]
    global_shifts = [(active_energy+s)*math.tanh(contact/(active_energy+s))
                     for s in spectator_energies]
    cluster_shift = active_energy*math.tanh(contact/active_energy)
    assert global_shifts[0] == cluster_shift
    assert global_shifts[0] < global_shifts[-1] < contact
    # A real 16-dimensional SO(9) spinor is not needed to check the normalization:
    # a two-axis Pauli subalgebra gives the same centre-of-mass coefficient.
    momenta = np.array([.42, -.67])
    pplus = 1.9
    boost_block = (momenta[0]*np.array([[1.,0.],[0.,-1.]])
                   +momenta[1]*np.array([[0.,1.],[1.,0.]]))/(math.sqrt(2)*pplus)
    motion = 2*pplus*(boost_block@boost_block.T)
    assert np.max(abs(motion-(momenta@momenta)/pplus*np.eye(2))) < 2e-16
    return dict(polarizations=256, checked_anticommutators=256, spin_strength=strength,
                normalized_ward_error=float(defect), hellinger_squared=float(outcomes[0]),
                orbital_ward_error=0., stationary_completions=completions,
                spectator_energies=spectator_energies, total_energy_contact_shifts=global_shifts,
                isolated_cluster_shift=cluster_shift, light_front_kinetic_trace=float(np.trace(motion)/2))


def recoil_records_checks():
    return dict(clock=check_clock(), closed_exchange=check_closed_exchange(),
                matrix_pairs=check_pairs(), gravity_echo=check_gravity_echo(),
                gravitational_pulses=check_pulse_reads(), energy_floor=check_positive_energy(), falling_source=check_infall(), supercharge=check_supercharges())


def draw_recoil_records(root):
    fig, axes = plt.subplots(1, 2, figsize=(8.5, 3.15), layout="constrained")
    s = np.geomspace(.065, 5, 420)
    axes[0].semilogx(s, clock_contrast(s), label="Sharp recoil", color="#275272")
    spread = sum(w*clock_contrast(a*s) for a, w in zip([.17,.8,3.9], [.15,.55,.3]))
    axes[0].semilogx(s, spread, label="Three rapidities", color="#a55826", ls="--")
    axes[0].axhline(0, color="0.5", lw=.6)
    axes[0].set(xlabel="Common Doppler scale", ylabel="Difference of excitation probabilities",
                title="A clock that can recoil")
    t = np.geomspace(.025, 3, 250)
    n = np.arange(45)
    for mean, color in ((1., "#275272"), (5., "#a55826")):
        upper = poisson.pmf(n, mean)@np.tanh(np.outer(n, t)/2)
        axes[1].semilogx(t, upper, color=color, label=f"Collective, mean {mean:g}")
        axes[1].semilogx(t, -np.expm1(-mean*np.tanh(t/2)), color=color, ls="--")
    axes[1].set(xlabel=r"Amplitude decay rate times spacing $\gamma T/2$",
                ylabel="Probability of a correct mark", title="Resolving a train of possible arrivals")
    for axis in axes:
        axis.legend(frameon=False, fontsize=8)
        axis.spines[["top", "right"]].set_visible(False)
    fig.savefig(root/"manuscripts/gravitational_recoil_records.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)
