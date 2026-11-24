"""Compare the parity-even ordinary matrix determinant and CAT charge readout.

Run from any directory. Lengths in the numerical examples are circumferences;
hbar is set to one. The results apply to the multiplication-operator sector.
"""

import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad


def tensor_product(factors):
    result = np.array([[1.0]])
    for factor in factors:
        result = np.kron(result, factor)
    return result


def gamma_matrices(pairs):
    identity = np.eye(2)
    x = np.array([[0, 1], [1, 0]])
    y = np.array([[0, -1j], [1j, 0]])
    z = np.diag([1, -1])
    gammas = []
    for index in range(pairs):
        for pauli in (x, y):
            gammas.append(tensor_product([z]*index + [pauli] + [identity]*(pairs-index-1)))
    return gammas, tensor_product([z]*pairs)


def matrix_spectra():
    gammas10, chirality = gamma_matrices(5)
    gammas9, ninth = gamma_matrices(4)
    gammas9.append(ninth)
    chiral = np.where(np.diag(chirality) > 0)[0]
    spectra = []
    for nx, ny, k, lengths in ((1, 0, 1, (1., 1., 1.)), (2, -3, 1, (.8, 1.3, 2.)),
                                (0, 2, -2, (2., .75, 1.5)), (.5, 1, 2, (1., 1., 2.))):
        fiber, base2, base3 = lengths
        cross = (2*np.pi*k/(base2*base3))*np.array([[-nx, ny], [ny, nx]])
        field = np.block([[np.zeros((2, 2)), cross], [-cross.T, np.zeros((2, 2))]])
        magnetic = 2*np.pi*abs(k)*np.hypot(nx, ny)/(base2*base3)
        kinetic_floor = (2*np.pi*np.hypot(nx, ny)/fiber)**2
        assert np.allclose(field@field, -magnetic**2*np.eye(4))

        def spin(gammas):
            return sum(1j*field[i, j]*(gammas[i]@gammas[j])
                       for i in range(4) for j in range(i+1, 4))

        vector = np.linalg.eigvalsh(2j*field)/magnetic
        # Six inactive vector directions, two cancelled by the complex ghost.
        vector = np.sort(np.r_[vector, np.zeros(4)])
        ikkt = np.linalg.eigvalsh(spin(gammas10)[np.ix_(chiral, chiral)])/magnetic
        bfss = np.linalg.eigvalsh(spin(gammas9))/magnetic
        for spinor in (ikkt, bfss):
            np.testing.assert_allclose(spinor, np.repeat(vector, 2), atol=2e-14)
        multiplicities = [int(np.isclose(vector, shift).sum()) for shift in (-2, 0, 2)]
        assert multiplicities == [2, 4, 2]
        spectra.append(dict(momentum=[nx, ny], twist_integer=k, lengths=list(lengths),
                            shifts_over_B=[-2, 0, 2], real_vector_multiplicities=multiplicities,
                            ikkt_weyl_and_bfss_spin_multiplicities=[2*m for m in multiplicities],
                            lowest_mass_squared=kinetic_floor))
    return spectra


def winding_potential(base2, base3, cutoff):
    coordinates = np.arange(-cutoff, cutoff+1)
    radii = coordinates[:, None]**2+coordinates[None, :]**2
    odd_weights = np.broadcast_to(2*(coordinates[:, None] % 2), radii.shape)
    first = np.bincount(radii.ravel(), weights=odd_weights.ravel())
    second = np.bincount(radii.ravel())
    i, j = np.flatnonzero(first), np.flatnonzero(second)
    distance2 = base2**2*i[:, None] + base3**2*j[None, :]
    lattice_sum = np.sum(first[i, None]*second[None, j]/distance2**4)
    return -24*(base2*base3)**2*lattice_sum/np.pi**4


def proper_time_potential(base2, base3):
    # theta_B-theta_F; the winding representation avoids cancellation at small t.
    integers = np.arange(-20, 21)

    def integrand(t):
        if t < .1:
            normal = np.exp(-base2**2*integers**2/(4*t))
            odd = normal*(2*(integers % 2))
            base = np.exp(-base3**2*integers**2/(4*t))
            difference = (base2*base3)**2/(4*np.pi*t)**2*odd.sum()*normal.sum()*base.sum()**2
        else:
            scale = 4*np.pi**2*t
            p = np.exp(-scale*(integers/base2)**2).sum()
            ap = np.exp(-scale*((integers+.5)/base2)**2).sum()
            p3 = np.exp(-scale*(integers/base3)**2).sum()
            difference = (p-ap)*p*p3**2
        return difference/t**3

    integral = sum(quad(integrand, a, b, epsabs=2e-10, epsrel=2e-11)[0]
                   for a, b in ((0., .1), (.1, 1.), (1., np.inf)))
    return -4*integral/(4*np.pi)**2


def boundary_conditions():
    cases = []
    for base2, base3 in ((1., 1.), (.85, 1.3)):
        reference = proper_time_potential(base2, base3)
        approximations = [winding_potential(base2, base3, cutoff) for cutoff in (12, 24, 48)]
        errors = [abs(value/reference-1) for value in approximations]
        assert errors[2] < errors[1] < errors[0] and errors[2] < 2e-7
        displacement = .07
        dilation = np.exp(.75*displacement)
        after = np.exp(-12*displacement)*proper_time_potential(dilation*base2, dilation*base3)
        np.testing.assert_allclose(after/reference, np.exp(-15*displacement), rtol=1e-10)
        cases.append(dict(base_lengths=[base2, base3], heat_integral=reference,
                          winding_cutoffs=[12, 24, 48], winding_estimates=approximations,
                          measured_scaling_weight=np.log(after/reference)/displacement))
    return cases


def central_twist():
    # theta difference on Z^2 and Z^2+(1/2,0); jet in proper time, computed
    # from ordinary Gaussian derivatives in complementary representations.
    axis = np.arange(-15, 16)
    periodic = (axis[:, None]**2+axis[None, :]**2).ravel()
    shifted = ((axis[:, None]+.5)**2+axis[None, :]**2).ravel()
    winding = periodic.reshape(31, 31)[axis % 2 == 1, :].ravel()*np.pi**2

    def jet(u, order):
        if u < 2.:
            x = winding/u
            polynomial = (np.ones_like(x), x-1, x**2-4*x+2)[order]
            return 2*np.pi*np.sum(np.exp(-x)*polynomial)/u**(1+order)
        return sum(sign*np.sum((-squares)**order*np.exp(-u*squares))
                   for sign, squares in ((1, periodic), (-1, shifted)))

    axis_z = np.arange(-80, 81)
    radius2 = axis_z[axis_z % 2 == 1, None]**2+axis_z[None, :]**2
    sums = [float(np.sum(2./radius2**(p/2))) for p in (10, 8, 6)]
    expected = [24*sums[0]/np.pi**9, -18*sums[1]/np.pi**7, 4*sums[2]/np.pi**5]
    moments = []
    for order in range(3):
        def integral(u):
            return (-1)**order*u**(2*order-5)*jet(u, order)
        moments.append(sum(quad(integral, a, b, epsabs=3e-12, epsrel=5e-11)[0]
                           for a, b in ((0., 2.), (2., 30.), (30., np.inf))))
    np.testing.assert_allclose(moments, expected, rtol=3e-8)
    epsilon = .25
    curvature_errors = [9/4*32*6/675*epsilon**6, 9/4*60*2/10395*15480*epsilon**8,
                        9/4*96*44*5040*192/3**12*epsilon**10]
    curvature_floor = 432/4**7
    assert sum(curvature_errors) < curvature_floor
    # Differentiate the unexpanded heat trace. Both regulators are varied;
    # the analytic estimate above covers the omitted tail independently.
    def curvature_integral(minimum_u, cutoff):
        lattice = np.arange(-cutoff, cutoff+1)
        r0 = (lattice[:, None]**2+lattice[None, :]**2).ravel()
        rh = ((lattice[:, None]+.5)**2+lattice[None, :]**2).ravel()
        squares = np.r_[r0[r0 > 0], rh]
        sign = np.r_[np.ones((r0 > 0).sum()), -np.ones(rh.size)]
        def integrand(u):
            selected = squares*u < 60
            r2 = squares[selected]
            y = epsilon*np.sqrt(r2)*u
            coth = 1/np.tanh(y)
            c2 = coth**2
            response = 2*y**2*(c2-1)*(3*c2-1)-2*y*coth*(c2-1)-4*c2
            return -2.25*np.sum(sign[selected]*r2*np.exp(-u*r2)*response)/u**3
        return sum(quad(integrand, a, b, epsabs=3e-10, epsrel=2e-9)[0]
                   for a, b in ((minimum_u, 1.), (1., 5.), (5., 40.), (40., 240.)))
    direct = [curvature_integral(.2, 20), curvature_integral(.3, 25)]
    leading = -108*sums[1]/np.pi**7
    assert max(abs(value-leading) for value in direct) < sum(curvature_errors)
    np.testing.assert_allclose(*direct, atol=3e-9, rtol=5e-8)
    return dict(center_shift=[.5, 0], minimum_even_twist=2, zeta_cutoff=80,
                winding_sums_Z10_Z8_Z6=sums, heat_moments=moments,
                leading_Einstein_weights=[-9, -12, -15],
                curvature_test=dict(maximum_aspect_parameter=epsilon, error_bounds=curvature_errors,
                    absolute_leading_lower_bound=curvature_floor,
                    strict_margin=curvature_floor-sum(curvature_errors),
                    direct_heat_integrals=direct, leading_value=leading),
                coefficients_after_powers_of_lengths_and_k=[-96*sums[0]/np.pi**5,
                    12*sums[1]/np.pi**5, -sums[2]/(15*np.pi**5)])


def charge_readout():
    # C4: six distinct positive weights on four contacts of three layers.
    incidence = np.array([[1., -1., 0.], [1., 0., -1.], [0., 1., -1.], [1., -1., 0.]])
    gaps = []
    for q in np.linspace(-.8, .8, 6):
        weights = np.exp(q*np.array([-2., 1., .5, 3.]))
        gram = incidence.T@(weights[:, None]*incidence)
        eigenvalues, eigenvectors = np.linalg.eigh(gram)
        null = eigenvectors[:, :1]@eigenvectors[:, :1].T
        np.testing.assert_allclose(null, np.ones((3, 3))/3, atol=2e-14)
        gaps.append(float(eigenvalues[1]))
    # Conditional records distinguish band position. An independent exact
    # Fourier calculation checks mean momentum and its variance after a write.
    count = 128
    q = 2*np.pi*np.arange(count)/count
    momentum = np.fft.fftfreq(count)*count
    wave = (1+.2*np.cos(2*q))*np.exp(3j*q)
    wave /= np.linalg.norm(wave)
    def moments(state):
        spectrum = abs(np.fft.fft(state, norm='ortho'))**2
        return np.array([np.sum(spectrum*p) for p in (1, momentum, momentum**2)])
    input_moments = moments(wave)
    cases = []
    for phase in (0, 2):
        amplitudes = [np.cos(q), np.sin(q)*np.exp(1j*phase*q)]
        output = sum(moments(k*wave) for k in amplitudes)
        # a=phase*sin(q)^2, sum |k'|^2=1+phase^2*sin(q)^2.
        derivative = np.fft.ifft(1j*momentum*np.fft.fft(wave))
        a = phase*np.sin(q)**2
        predicted_p = input_moments[1]+np.sum(a*abs(wave)**2)
        predicted_p2 = np.sum(abs(-1j*derivative+a*wave)**2 +
                              (1+phase**2*np.sin(q)**2-a**2)*abs(wave)**2)
        np.testing.assert_allclose(output, [1, predicted_p, predicted_p2], atol=5e-13)
        cases.append(dict(port_phase_winding=phase, mean_momentum_change=output[1]-input_moments[1],
                          mean_square_momentum_change=output[2]-input_moments[2]))
    return dict(positive_relative_gaps=gaps, common_projector_diagonal=1/3, readout_examples=cases)


def charge_and_force():
    rng = np.random.default_rng(181)
    # Four radius bins, two charge values. The incoming state need not factor.
    dimension = 8
    def complex_array(shape):
        return rng.normal(size=shape)+1j*rng.normal(size=shape)
    state = complex_array((dimension, 5))
    density = state@state.conj().T
    density /= np.trace(density)
    ordinary, _ = np.linalg.qr(complex_array((dimension, dimension)))
    incident = ordinary@density@ordinary.conj().T
    p = np.kron(np.eye(4), np.diag([1., 0.]))
    other = np.eye(dimension)-p
    written = p@incident@p + other@incident@other
    operator = complex_array((4, 4))
    radius = np.kron(operator+operator.conj().T, np.eye(2))
    np.testing.assert_allclose(np.trace(radius@(written-incident)), 0., atol=2e-14)
    joint = complex_array((dimension, dimension))
    force = joint+joint.conj().T
    measured = np.trace(force@(written-incident)).real
    cross = np.trace((p@force@other + other@force@p)@incident).real
    np.testing.assert_allclose(measured, -cross, atol=2e-14)
    # Distinct neutral pairs from the same kinetic spectrum, E_f(0)=E_b(0)=1.
    def pair_energy(s, base):
        length = np.exp(.75*s) if base else 1.
        return np.exp(-3*s)/length
    h = 1.e-5
    slopes = [-(pair_energy(h, base)-pair_energy(-h, base))/(2*h) for base in (False, True)]
    np.testing.assert_allclose(slopes, [3., 15/4], rtol=3e-10)
    ratios = []
    for mu2 in (0., .3, 1., 9.):
        for landau in (0., 2., 4., 24.):
            if mu2+landau == 0:
                continue
            def energy(s):
                return np.sqrt(mu2*np.exp(-6*s)+landau*np.exp(-7.5*s))
            ratio = -(energy(h)-energy(-h))/(2*h*energy(0.))
            np.testing.assert_allclose(ratio, 3.+.75*landau/(mu2+landau), rtol=5e-10)
            ratios.append(ratio)
    return dict(random_seed=181, write_induced_force_difference=measured,
                lost_off_diagonal_force=cross, pair_forces_per_crossing_energy=slopes,
                maximum_change_per_crossing_energy=slopes[1]-slopes[0],
                bulk_rest_force_ratios=[float(min(ratios)), float(max(ratios))])


def main():
    result = dict(static_sector=matrix_spectra(), base_spin_twist=boundary_conditions(),
                  central_spin_twist=central_twist(), cat_contacts=charge_readout(),
                  force_at_contact=charge_and_force())
    target = Path(__file__).resolve().parents[1]/'verification'/'cat-radius-comparison-results.json'
    target.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')


if __name__ == '__main__':
    main()
