"""Project the six CAT scalars, track physical connecting modes, and test a material clock."""
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import block_diag
from scipy.special import mathieu_a, mathieu_b


SPIN = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]]) / 2
OMEGA = np.sqrt(2.0)
ROOT = np.exp(2j * np.pi / 3)


def embed(field, labels):
    """Hermitian coordinates with the two tetrahedral projections imposed."""
    phases = ROOT ** np.array(labels)
    complex_axes = [np.kron(spin, (phases[:, None] / phases[None, :]) ** i * field)
                    for i, spin in enumerate(SPIN)]
    return np.array([part for axis in complex_axes for part in
                     ((axis + axis.conj().T) / 2, (axis - axis.conj().T) / (2j))])


def comm(a, b):
    return a @ b - b @ a


def bare_hessian(background, left, right):
    """Second derivative of the original commutator energy, before subtracting rotation."""
    value = 0.
    for i, j in itertools.combinations(range(6), 2):
        first = comm(left[i], background[j]) + comm(background[i], left[j])
        second = comm(right[i], background[j]) + comm(background[i], right[j])
        mixed = comm(left[i], right[j]) + comm(right[i], left[j])
        value += (np.vdot(first, second) + np.vdot(comm(background[i], background[j]), mixed)).real
    return value


def projection():
    half_turn = 2j * SPIN[0]
    third_turn = np.eye(2) / 2 - 1j * sum(SPIN)
    colour = [np.eye(2) / np.sqrt(2), *(np.sqrt(2) * SPIN)]
    def rotation(unitary):
        return np.array([[np.vdot(a, unitary @ b @ unitary.conj().T)
                          for b in colour] for a in colour]).real
    group = [np.eye(4)]
    for element in group:
        for generator in (rotation(half_turn), rotation(third_turn)):
            candidate = element @ generator
            if not any(np.allclose(other, candidate) for other in group):
                group.append(candidate)
    assert len(group) == 12
    projector = sum(np.kron(g[1:, 1:], g) for g in group) / 12
    np.testing.assert_allclose(projector @ projector, projector, atol=2e-15)
    assert np.linalg.matrix_rank(projector, tol=1e-8) == 1
    rng = np.random.default_rng(173)
    field = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
    axes = embed(field, (0, 1, 2))[::2] + 1j * embed(field, (0, 1, 2))[1::2]
    for unitary, chars in ((half_turn, np.ones(3)), (third_turn, ROOT ** np.arange(3))):
        lift = np.kron(unitary, np.diag(chars))
        image = np.array([lift @ axis @ lift.conj().T for axis in axes])
        rot = rotation(unitary)[1:, 1:]
        np.testing.assert_allclose(image, np.einsum("ji,jab->iab", rot, axes), atol=2e-14)
    assert abs(np.trace(third_turn)) > .9
    np.testing.assert_allclose(sum(ROOT ** np.arange(3)), 0, atol=1e-14)
    return dict(group_order=12, scalar_intertwiners_per_ordered_pair=1,
                single_spin_scalar_dimension_complex=1,
                balanced_three_spin_scalar_dimension_complex=9)


def connecting_hessian():
    directions = []
    for i, j in ((0, 1), (1, 0)):
        for coefficient in (1, 1j):
            field = np.zeros((2, 2), complex)
            field[i, j] = coefficient
            directions.append(embed(field, (0, 1)))
    inertia = np.vdot(directions[0], directions[0]).real
    np.testing.assert_allclose(inertia, 1.5)
    pairs = [(1, 1), (1, 0), (1, 1j), (1, -1), (.73-.4j, -1.2+.26j)]
    for a, b in pairs:
        background = embed(np.diag([a, b]), (0, 1))
        independent = np.array([[bare_hessian(background, left, right) / inertia
                                 for left in directions] for right in directions])
        h = abs(a + b) ** 2 / 4
        gap = -(a ** 2 + b ** 2) / 2
        block = np.array([[gap.real, gap.imag], [gap.imag, -gap.real]])
        expected = h * np.eye(4) + np.block([[np.zeros((2, 2)), block], [block, np.zeros((2, 2))]])
        np.testing.assert_allclose(independent, expected, atol=3e-14)
    rows = []
    for degrees in (0, 30, 60, 90, 120, 180):
        cosine = np.cos(np.deg2rad(degrees))
        centre = (3 - cosine) / 2
        peak_k2 = centre - cosine ** 2 / 8
        gyroscope = block_diag(*([np.array([[0., -1.], [1., 0.]])] * 2))
        background = embed(np.diag([1, np.exp(1j*np.deg2rad(degrees))]), (0, 1))
        mass = np.array([[bare_hessian(background, u, v) / inertia for u in directions]
                         for v in directions]) - 2*np.eye(4)
        generator = np.block([[np.zeros((4, 4)), np.eye(4)],
                              [-mass - peak_k2*np.eye(4), -2*OMEGA*gyroscope]])
        rate = max(np.linalg.eigvals(generator).real) / OMEGA
        np.testing.assert_allclose(rate, abs(cosine)/4, atol=5e-8)
        rows.append(dict(degrees=degrees, band_k2=np.round([centre-abs(cosine), centre+abs(cosine)], 9).tolist(),
                         maximum_growth_over_omega=round(abs(cosine)/4, 9)))
    return rows


def propagate(rhs, size, period, real=False):
    state = np.eye(size, dtype=float if real else complex)
    def derivative(t, column):
        return (rhs(t) @ column.reshape(size, size)).ravel()
    answer = solve_ivp(derivative, (0, period), state.ravel(), method="DOP853",
                       rtol=1e-10, atol=3e-12)
    assert answer.success
    return answer.y[:, -1].reshape(size, size)


def unequal_growth(ratio, sign, k):
    # The change to the mean rotating frame makes every two-node problem periodic.
    beat = OMEGA * (1-sign*ratio)
    mean = OMEGA * (1+sign*ratio)/2
    period = 2*np.pi/abs(beat)
    identity, zero = np.eye(2), np.zeros((2, 2))
    def generator(time):
        phase = np.exp(1j*beat*time)
        h = (1+ratio**2+2*ratio*phase.real)/4
        gap = -(phase + ratio**2*phase.conjugate())/2
        mass = (k*k+h-mean*mean)*identity + np.array([[0, gap], [gap.conjugate(), 0]])
        return np.block([[zero, identity], [-mass, -2j*mean*np.diag([1., -1.])]])
    transfer = propagate(generator, 4, period)
    eigenvalues = np.linalg.eigvals(transfer)
    growth = np.log(max(abs(eigenvalues))) / (period*OMEGA)
    return growth


def beat_tests():
    opposite = []
    for q in (1/8, 3/8):
        def generator(t):
            return np.array([[0., 1.], [-1+2*q*np.cos(2*t), 0.]])
        transfer = propagate(generator, 2, np.pi, real=True)
        trace = np.trace(transfer)
        assert mathieu_b(1, q) < 1 < mathieu_a(1, q) and trace < -2
        np.testing.assert_allclose(np.linalg.det(transfer), 1., atol=6e-11)
        opposite.append(dict(q=q, trace=round(trace, 9),
                             growth_over_omega=round(np.arccosh(-trace/2)/np.pi, 9)))
    np.testing.assert_allclose(unequal_growth(1., -1, np.sqrt(1.5)),
                               opposite[1]["growth_over_omega"], atol=2e-8)
    sampled = []
    for ratio in (.25, .5, .75):
        for sign in (1, -1):
            trials = [(unequal_growth(ratio, sign, k), k) for k in (.65, .95, 1.2, 1.45)]
            growth, k = max(trials)
            assert growth > .005
            sampled.append(dict(smaller_over_larger_radius=ratio, helicity=sign, k_over_large_radius=k,
                                witnessed_growth_over_large_omega=round(growth, 8)))
    return dict(equal_opposite=opposite, unequal_witnesses=sampled)


def lapse_and_force():
    # Solve both static equations independently of eliminating the condensate.
    inertia, radius, planck = 1.7, .83, 500.
    mass_sq = 4*radius**2
    for k, a, b in itertools.product((.13, 1.9, 7.), (0., .27, 1.), (.2, 1.)):
        denominator = k*k+mass_sq
        linear = np.array([[denominator, 4*radius**3],
                           [4*inertia*radius**3, 2*planck**2*k*k-2*inertia*radius**4]])
        u, phi = np.linalg.solve(linear, [-a/(inertia*radius), -1.])
        chi = 2*inertia*radius**4 + 16*inertia*radius**6/denominator
        force = -(1-a*mass_sq/denominator)*(1-b*mass_sq/denominator)/(2*planck**2*k*k-chi)
        force -= a*b/(inertia*radius**2*denominator)
        np.testing.assert_allclose(phi+b*u/radius, force, rtol=8e-13, atol=1e-15)
    # Diagonalise the helicity-resolved fermion Hamiltonian at the minimum.
    for helicity, p in itertools.product((-1, 1), (0., OMEGA/2, 1.7)):
        diagonal = helicity*p-OMEGA/2
        ham = np.array([[diagonal, 2.], [2., -diagonal]])
        np.testing.assert_allclose(np.linalg.eigvalsh(ham)[1], np.hypot(diagonal, 2.))
    hbar_c, hbar_ev_s, light_speed = 1.973269804e-7, 6.582119569e-16, 299792458.
    hubble = 67.4e3 / 3.085677581491367e22
    reduced_planck_ev = 2.435e27
    critical_density = 3*reduced_planck_ev**2*(hbar_ev_s*hubble)**2
    largest_radius = (critical_density/(9/4))**.25
    minimum_range = hbar_c/(2*largest_radius)
    cassini = np.array([2.1 - 1.96*2.3, 2.1 + 1.96*2.3])*1e-5
    return dict(critical_density_eV4=critical_density, max_r_for_g1_eV=largest_radius,
                min_range_for_g1_m=minimum_range,
                unit_force_slope_at_this_range=2*hubble*minimum_range/light_speed,
                cassini_universal_s_approx95=(cassini/(2+cassini)).tolist(),
                clock_pair_gap_over_radius=4., single_fermion_gap_over_radius=2.)


def occupied_waves():
    """Compare adiabatic finite differences against the shape correction after radial balance."""
    shape = np.array([1., 1., -2.])/np.sqrt(6)
    rows = []
    for ell, p in itertools.product((1, 2, 4), (0., 1.25)):
        l2 = ell*(ell+1)
        magnetic = np.arange(-ell, ell+1)
        raising = np.diag(np.sqrt(l2-magnetic[:-1]*(magnetic[:-1]+1)), -1)
        generators = [(raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(magnetic)]
        squares = np.array([j@j for j in generators])
        def energy(amplitudes):
            kernel = np.einsum("i,iab->ab", amplitudes**2, squares)
            return np.mean(np.sqrt(p*p+np.linalg.eigvalsh(kernel)))
        step = .0003
        unit = np.ones(3)
        radial_force = (energy((1+step)*unit)-energy((1-step)*unit))/(6*step)
        hessian = (energy(unit+step*shape)-2*energy(unit)+energy(unit-step*shape))/step**2
        stiffness = -l2*(4*l2-3)/(30*(p*p+l2)**1.5)
        np.testing.assert_allclose(hessian-radial_force, stiffness, rtol=2e-6, atol=3e-8)
        rows.append(dict(ell=ell, momentum_over_r=p, balanced_shape_correction=round(stiffness, 9)))
    return rows


def two_internal_spheres():
    # Read both the KK Laplacian and the double flux commutator from matrices.
    def generators(n):
        j = (n-1)/2
        magnetic = np.arange(-j, j+1)
        raising = np.diag(np.sqrt(j*(j+1)-magnetic[:-1]*(magnetic[:-1]+1)), -1)
        return ((raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(magnetic))
    rows = []
    for n, m in ((2, 2), (2, 3), (3, 3)):
        size = n*m
        identity = np.eye(size)
        def adjoint(a):
            return np.kron(identity, a)-np.kron(a.T, identity)
        for t in (.224744871391589, 1., 2.6):
            coordinates = [np.kron(j, np.eye(m)) for j in generators(n)]
            coordinates.extend(np.sqrt(t)*np.kron(np.eye(n), j) for j in generators(m))
            lap = sum(adjoint(a) @ adjoint(a) for a in coordinates)
            flux = [adjoint(1j*comm(a,b)) for a,b in itertools.combinations(coordinates, 2)]
            direct = np.trace(np.linalg.pinv(lap, rcond=1e-12, hermitian=True) @
                              sum(f @ f for f in flux)).real
            trace = sum((2*l+1)*(2*j+1)*(l*(l+1)+t*t*j*(j+1))/(l*(l+1)+t*j*(j+1))
                        for l in range(n) for j in range(m) if l+j)
            np.testing.assert_allclose(direct, trace, rtol=5e-13)
            rows.append(dict(ranks=[n,m], squared_scale_ratio=t, normalized_newton_trace=round(trace, 9)))
    def f(t):
        return 6*(2*t*t+t+2)/(1+t)
    neutral = np.sqrt(1.5)-1
    h = .0004
    np.testing.assert_allclose((f(neutral+h)-f(neutral-h))/(2*h), 0, atol=2e-6)
    def shape(t):
        return -f(t)**2/(1+t*t)
    np.testing.assert_allclose((shape(1+h)-2*shape(1)+shape(1-h))/h**2, -11.25, rtol=2e-6)
    return dict(traces=rows, neutral_first_factor_t=neutral, optimized_energy_shape_curvature=-11.25)


def rotating_product():
    """The transverse colour singlet survives the simultaneous tetrahedral rotation."""
    first = np.array([np.kron(j, np.eye(2)) for j in SPIN])
    second = np.array([np.kron(np.eye(2), j) for j in SPIN])
    probe = sum(a@b for a,b in zip(first, second))
    for total in first + second:
        np.testing.assert_allclose(comm(total, probe), 0., atol=1e-14)
    ratio = np.sqrt(np.sqrt(1.5)-1)
    rows = []
    for sign in (1, -1):
        beat = OMEGA * abs(1-sign*ratio)
        q = 8*ratio/beat**2
        minimum_a = 8*(1+ratio**2)/beat**2
        for order in range(1, 20):
            low, high = sorted((mathieu_a(order, q), mathieu_b(order, q)))
            if high > minimum_a:
                break
        else:
            raise AssertionError("No low-order physical gap in the chosen example")
        a = (max(low, minimum_a)+high)/2
        k = np.sqrt(a*beat**2/4-2*(1+ratio**2))
        def physical(time):
            internal = np.exp(1j*OMEGA*time)*first + ratio*np.exp(1j*sign*ratio*OMEGA*time)*second
            lap = sum(comm(herm, comm(herm, probe)) for axis in internal
                      for herm in ((axis+axis.conj().T)/2, (axis-axis.conj().T)/(2j)))
            traced = np.vdot(probe, lap).real / np.vdot(probe, probe).real
            predicted = 2*(1+ratio**2)-4*ratio*np.cos(beat*time)
            np.testing.assert_allclose(lap, predicted*probe, atol=9e-13)
            return np.array([[0., 1.], [-k*k-traced, 0.]])
        transfer = propagate(physical, 2, 2*np.pi/beat, real=True)
        trace = np.trace(transfer)
        assert abs(trace) > 2.001
        rows.append(dict(helicity=sign, mathieu_gap=order, k_over_r=round(k, 9),
                         monodromy_trace=round(trace, 9),
                         growth_over_r=round(beat*np.arccosh(abs(trace)/2)/(2*np.pi), 9)))
    return rows


if __name__ == "__main__":
    result = dict(projection=projection(), connecting_shapes=connecting_hessian(),
                  beats=beat_tests(), matter=lapse_and_force(), occupied_waves=occupied_waves(),
                  static_product=two_internal_spheres(), rotating_product=rotating_product())
    path = Path(__file__).resolve().parents[1]/"verification"/"cat-tetrahedral-radius-results.json"
    path.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
