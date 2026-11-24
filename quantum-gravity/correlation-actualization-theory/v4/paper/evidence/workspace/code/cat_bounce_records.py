"""Material modes, exact radar and a magnetic-flux reader on two membranes (T.15)."""
import argparse
import json
from itertools import combinations
from pathlib import Path

import numpy as np
from numpy.polynomial import polynomial as poly
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import ellipj, ellipk, ndtr

from cat_graviton_port import Receiver


def integrate(rhs, interval, initial, **options):
    solution = solve_ivp(rhs, interval, initial, method="DOP853", rtol=2e-11,
                         atol=2e-13, **options)
    assert solution.success, solution.message
    return solution


def radial_orbit(h):
    root = np.sqrt(1+4*h*h)
    lower, upper = (-1-root)/2, (root-1)/2
    rate = np.sqrt(1-lower)
    modulus = (1-upper)/(1-lower)
    quarter = ellipk(modulus)

    def radius2(t):
        sn = ellipj(rate*t+quarter, modulus)[0]
        return 1-(1-upper)*sn*sn

    return np.array([lower, upper, 1.]), 2*quarter/rate, radius2


def monodromy(h, degree):
    roots, period, radius2 = radial_orbit(h)
    casimir = degree*(degree+1)

    def rhs(t, y):
        return y[2], y[3], -casimir*radius2(t)*y[0], -casimir*radius2(t)*y[1]

    end = integrate(rhs, (0, period), [1., 0., 0., 1.]).y[:, -1].reshape(2, 2)
    np.testing.assert_allclose(np.linalg.det(end), 1., atol=4e-10)
    omega = np.sqrt(casimir*roots[1])
    scaling = np.diag([np.sqrt(omega), 1/np.sqrt(omega)])
    normalized = scaling@end@np.linalg.inv(scaling)
    records = []
    for n in (1, 3, 6, 10):
        transfer = np.linalg.matrix_power(normalized, n)
        occupation = max(0., (np.linalg.norm(transfer)**2-2)/4)
        records.append(dict(periods=n, occupation=occupation,
                            excited=1-1/np.sqrt(1+occupation)))
    trace = float(np.trace(end))
    # At an unresolved double root the characteristic roots lose half the digits.
    multiplier = 1. if abs(abs(trace)-2) < 2e-9 else max(abs(np.linalg.eigvals(end)))
    return end, dict(h=h, degree=degree, period=period, trace=trace,
                     multiplier=float(multiplier), readouts=records)


def lame_edges(h):
    """Eleven band edges from polynomial Lamé eigenfunctions, without time evolution."""
    roots, _, _ = radial_orbit(h)
    cubic = -4*poly.polyfromroots(roots)
    edges = []
    for count in (1, 3):
        degree = (5-count)//2
        nodes = roots[1]+(1-roots[1])*np.linspace(.19, .84, degree+1)
        basis = poly.polyvander(nodes, degree)
        f, df = poly.polyval(nodes, cubic), poly.polyval(nodes, poly.polyder(cubic))
        for chosen in combinations(roots, count):
            distances = nodes[:, None]-np.array(chosen)
            log_d = .5*(1/distances).sum(axis=1)
            log_dd = -.5*(1/distances**2).sum(axis=1)
            columns = []
            for k in range(degree+1):
                value, d1, d2 = nodes**k, k*nodes**(k-1), k*(k-1)*nodes**(k-2)
                columns.append(-(f*(d2+2*log_d*d1+(log_dd+log_d**2)*value)
                                 +.5*df*(d1+log_d*value)+30*nodes*value))
            eigenvalues = np.linalg.eigvals(np.linalg.solve(basis, np.array(columns).T))
            assert np.max(abs(eigenvalues.imag)) < 2e-7
            edges.extend(eigenvalues.real)
    return np.sort(edges)


def cutoff_scan():
    rows = []
    threshold = np.sqrt(5)/4
    for h in (.12, .25, .5, threshold, .62, .75, 1.):
        _, result = monodromy(h, 5)
        edges = lame_edges(h)
        d = h*h
        exact = -108*135**3*(1+d)*d*(5-16*d)*(80+496*d-25*d*d)
        if h != threshold:
            np.testing.assert_allclose(np.prod(-edges)/exact, 1., atol=3e-11)
        closest = int(np.argmin(abs(edges)))
        result.update(edge_near_zero=float(edges[closest]), edge_index=closest)
        roots, period, radius2 = radial_orbit(h)
        c = 1+d
        def radial_speed2(x):
            return max(0., 4*(x-roots[0])*(x-roots[1])*(1-x))
        def curvature_density(t):
            x = radius2(t)
            return (2*c-6*x*x)/(c-x*x)+1.5*x*radial_speed2(x)/(c-x*x)**2
        ricci = quad(curvature_density, 0., period, epsabs=3e-12, limit=160)[0]
        square = -quad(lambda x: x*np.sqrt(radial_speed2(x))/(c-x*x)**2,
                       roots[1], 1., epsabs=2e-11, epsrel=3e-11, limit=160)[0]
        np.testing.assert_allclose(ricci, square, rtol=1e-10, atol=2e-12)
        result.update(affine_length=quad(radius2, 0., period)[0], integrated_null_ricci=ricci)
        if h == threshold:
            assert abs(edges[closest]) < 5e-10 and abs(result["trace"]+2) < 5e-9
        else:
            assert (sum(edges < 0) % 2 == 0) == (h < threshold)
            assert (abs(result["trace"]) > 2) == (h < threshold)
        rows.append(result)
    return rows


def nonlinear_test():
    """Full commutators on seven 6x6 matrices. Two additional zero matrices stay zero."""
    n = 6
    spin = (n-1)/2
    weights = np.arange(-spin, spin+1)
    up = np.diag(np.sqrt((spin-weights[:-1])*(spin+weights[:-1]+1)), -1)
    axes = np.array([(up+up.T)/2, (up-up.T)/(2j), np.diag(weights)])
    harmonic = np.linalg.matrix_power(up, 5)
    harmonic = harmonic+harmonic.T
    harmonic /= np.linalg.norm(harmonic)

    def acceleration(x):
        brackets = x[:, None]@x[None, :]-x[None, :]@x[:, None]
        return -(x[:, None]@brackets-brackets@x[:, None]).sum(axis=0)

    def conserved(x, v):
        brackets = x[:, None]@x[None, :]-x[None, :]@x[:, None]
        energy = np.linalg.norm(v)**2/2+np.linalg.norm(brackets)**2/4
        gauss = np.linalg.norm((x@v-v@x).sum(axis=0))
        return energy, gauss

    h = .5
    roots, period, _ = radial_orbit(h)
    x0 = np.zeros((7, n, n), dtype=complex)
    v0 = np.zeros_like(x0)
    x0[:3] = np.sqrt(roots[1])*axes
    v0[3:6] = h/np.sqrt(roots[1])*axes
    transfer, _ = monodromy(h, 5)
    expected = np.linalg.matrix_power(transfer, 2)[:, 0]
    def angular_tensor(x, v):
        centers_x = x-x.trace(axis1=1, axis2=2)[:, None, None]*np.eye(n)/n
        centers_v = v-v.trace(axis1=1, axis2=2)[:, None, None]*np.eye(n)/n
        cross = (centers_x.reshape(7, -1)@centers_v.reshape(7, -1).conj().T).real
        return cross-cross.T

    rows = []
    for eps in (.04, .02, .01):
        x0[6] = eps*harmonic
        initial_energy, _ = conserved(x0, v0)
        initial_angular = angular_tensor(x0, v0)

        def rhs(_, y):
            x, v = y.reshape(2, *x0.shape)
            return np.stack((v, acceleration(x))).ravel()

        y = integrate(rhs, (0, 2*period), np.stack((x0, v0)).ravel()).y[:, -1]
        x, v = y.reshape(2, *x0.shape)
        energy, gauss = conserved(x, v)
        final_angular = angular_tensor(x, v)
        np.testing.assert_allclose(final_angular, initial_angular, atol=2e-10)
        assert np.linalg.matrix_rank(final_angular, tol=1e-8) == 6
        measured = np.array([np.vdot(harmonic, block[6]).real/eps for block in (x, v)])
        error = float(np.linalg.norm(measured-expected))
        assert abs(energy/initial_energy-1) < 5e-10 and gauss < 3e-9
        rows.append(dict(perturbation=eps, scaled_deviation=error,
                         relative_energy_drift=abs(energy/initial_energy-1),
                         gauss=gauss))
    assert 3.8 < rows[0]["scaled_deviation"]/rows[1]["scaled_deviation"] < 4.2
    assert 3.8 < rows[1]["scaled_deviation"]/rows[2]["scaled_deviation"] < 4.2
    return rows


def commuting_control():
    diagonal = np.array([[1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]])/2
    np.testing.assert_allclose(diagonal@diagonal.T, np.eye(3))
    currents = np.array([.5, .5, .5])
    energy = 1.875  # Round six-matrix solution, Tr(J_i J_i) normalized to one, h=1/2.
    radius = np.linalg.norm(currents)/np.sqrt(2*energy)
    x = np.vstack((radius*diagonal, np.zeros_like(diagonal)))
    v = np.vstack((np.zeros_like(diagonal), (currents/radius)[:, None]*diagonal))
    spin = x@v.T-v@x.T
    np.testing.assert_allclose(np.sort(np.linalg.svd(spin, compute_uv=False)), .5*np.ones(6))
    np.testing.assert_allclose(np.linalg.norm(v)**2/2, energy)
    assert np.linalg.matrix_rank(x) == 3
    return dict(normalized_energy=energy, angular_singular_values=[.5]*6, span=3, commutator_energy=0.)


def shared_source():
    """A phase-referenced incoming mode drives two identical material quadrupoles."""
    start, stop = -.5, 0.
    def orbit_rhs(_, y):
        return np.r_[y[2:], -2*np.dot(y[:2], y[:2])*y[:2]]

    orbit = integrate(orbit_rhs, (stop, start), [1., 0., 0., .5], dense_output=True)
    def shear_hessian(t):
        axis = orbit.sol(t)[:2]
        return 2*(np.dot(axis, axis)*np.eye(2)-np.outer(axis, axis))

    def response(t, y):
        # Smooth incoming tidal pulse of unit peak, with time measured at each receiver.
        phase = (t-start)/(stop-start)
        tide = np.exp(4-1/(phase*(1-phase))) if 0 < phase < 1 else 0.
        return np.r_[y[2:], -shear_hessian(t)@y[:2] - tide*np.array([orbit.sol(t)[0], 0.])]

    def modes(t, y):
        position, velocity = y.reshape(2, 2, 2)
        return np.stack((velocity, -shear_hessian(t)@position)).ravel()

    displacement = integrate(response, (start, stop), np.zeros(4)).y[:2, -1]
    assert displacement[0] < 0
    initial = np.stack((np.eye(2), -1j*np.eye(2))).ravel()/np.sqrt(2)
    basis = integrate(modes, (start, stop), initial).y[:4, -1].reshape(2, 2)
    sigma = .005
    covariance = (basis@basis.conj().T).real
    covariance *= sigma**2/covariance[0, 0]
    sd2 = np.sqrt(covariance[1, 1])
    conditional_shift = covariance[0, 1]/sd2
    conditional_sd = np.sqrt(sigma**2-conditional_shift**2)
    threshold = 2*sigma
    point = np.sqrt(.25-threshold**2)
    # The exact indicator of the spin-one-half port has a hyperbolic boundary in shear space.
    for d1 in (-.03, -.009, 0., .009, .03):
        for d2 in (0., .2, -.6):
            off_diagonal = (np.hypot(1+d1, d2)-np.hypot(1-d1, d2))/2
            level = np.linalg.eigvalsh([[.5-point, off_diagonal], [off_diagonal, .5+point]])[0]
            assert (level < 0) == (d1**2 > threshold**2*(1+d2**2/(1-threshold**2)))

    tidal_peak = sigma/abs(displacement[0])
    nodes, quadrature_weights = np.polynomial.hermite.hermgauss(48)
    rows = []
    for distance in (1, 2):
        # A four-dimensional radiative zero mode has far-zone amplitude proportional to 1/D.
        # The sign convention calls the displacement toward the positive material reference '+'.
        shift = -displacement*tidal_peak/distance
        for reference in (0., threshold):
            weights = []
            for mean in (np.array([reference, 0.])+shift, np.array([reference, 0.])-shift):
                def conditional_probability(z):
                    bound = threshold*np.sqrt(1+(mean[1]+sd2*z)**2/(1-threshold**2))
                    center = mean[0]+conditional_shift*z
                    return ndtr((center-bound)/conditional_sd)+ndtr((-center-bound)/conditional_sd)

                probability = np.dot(quadrature_weights, conditional_probability(np.sqrt(2)*nodes))/np.sqrt(np.pi)
                independent = quad(lambda z: np.exp(-z*z/2)*conditional_probability(z)/np.sqrt(2*np.pi),
                                   -12, 12, epsabs=1e-13)[0]
                np.testing.assert_allclose(probability, independent, atol=3e-13)
                weights.append(float(probability))
            contrast = abs(weights[0]-weights[1])
            rows.append(dict(distance_ratio=distance, reference_in_sigmas=reference/sigma,
                             negative_port_given_source=weights, discrimination=(1+contrast)/2))
            if reference == 0:
                assert contrast < 1e-15
    return dict(unit_peak_displacement=displacement.tolist(), covariance=covariance.tolist(),
                width=sigma, near_peak_tide=tidal_peak, port_position=point, readouts=rows)


def edge_absorption():
    """Compress the finite-time graviton amplitudes to actually occupied edge counts."""
    receiver = Receiver(1.)
    amplitudes, _ = receiver.amplitudes(4., 43)
    states = amplitudes[:, 0]
    filled, empty = receiver.frames(0.)[0]
    edge = receiver.probe.edge(receiver.orbits[0](0.))
    p, q = edge.conj().T@filled, edge.conj().T@empty
    samples = edge.shape[1]+1
    rotations = []
    for z in np.exp(2j*np.pi*np.arange(samples)/samples):
        sea = np.eye(filled.shape[1])+(z-1)*p.conj().T@p
        schur = np.eye(empty.shape[1])+(z-1)*q.conj().T@q
        schur -= (z-1)**2*q.conj().T@p@np.linalg.solve(sea, p.conj().T@q)
        rotations.append(np.linalg.det(sea)*schur)
    effects = np.fft.fft(rotations, axis=0)/samples
    np.testing.assert_allclose(effects.sum(axis=0), np.eye(empty.shape[1]), atol=3e-12)
    rows = []
    for count, effect in enumerate(effects):
        np.testing.assert_allclose(effect, effect.conj().T, atol=3e-12)
        assert min(np.linalg.eigvalsh(effect)) > -3e-12
        gram = np.array([[np.vdot(left, effect@right) for right in states] for left in states])
        np.testing.assert_allclose(gram, gram.conj().T, atol=5e-12)
        assert max(abs(gram[2, :2])) < 5e-12 and min(gram.diagonal().real) > 0
        background = gram[1:, 1:]
        clean = (gram[0, 0]-gram[0, 1:]@np.linalg.solve(background, gram[1:, 0])).real
        rows.append(dict(edge_count=count, absorption=float(gram[0, 0].real),
                         vacuum_emission=float(gram[1, 1].real),
                         ordinary=float(gram[2, 2].real), exclusive=float(clean)))
    return rows


def radar():
    """Freely falling clocks, in Rosen principal axes of a cross-polarized wave."""
    def rhs(u, y):
        bump = np.exp(4-1/(u*(1-u))) if 0 < u < 1 else 0.
        a, b, da, db, _, _ = y
        return da, db, bump*a, -bump*b, 1/a**2, 1/b**2

    solution = integrate(rhs, (0., 1.8), [1., 1., 0., 0., 0., 0.],
                         dense_output=True, max_step=.03)
    assert solution.y[:2].min() > .4

    def receiver_time(start, arm, sign):
        weights = (arm[0]+sign*arm[1])**2/2, (arm[0]-sign*arm[1])**2/2
        start_optical = solution.sol(start)[4:]
        def residual(end):
            integrated = solution.sol(end)[4:]-start_optical
            return (end-start)-np.dot(weights, 1/integrated)
        return brentq(residual, start+1e-5, start+.42, xtol=5e-15)

    def brinkmann_check(start, end, initial_arm, final_arm, sign):
        # Shoot the null ray between the two freely falling endpoints.
        def frame(arm, u):
            coordinates = np.array([arm[0]+sign*arm[1], arm[0]-sign*arm[1]])/np.sqrt(2)
            axes = solution.sol(u)
            position, velocity = axes[:2]*coordinates, axes[2:4]*coordinates
            return position, (u+position@velocity)/2
        def ray(u, y):
            bump = np.exp(4-1/(u*(1-u))) if 0 < u < 1 else 0.
            return np.r_[y[4:], bump*np.array([1, -1, 1, -1])*y[:4]]
        a, b, da, db = integrate(ray, (start, end), [1., 1., 0., 0., 0., 0., 1., 1.],
                                 max_step=.035).y[:, -1].reshape(4, 2)
        x0, v0 = frame(initial_arm, start)
        x1, v1 = frame(final_arm, end)
        slope = (x1-a*x0)/b
        residual = 2*(v1-v0)-x1@(da*x0+db*slope)+x0@slope
        assert abs(residual) < 3e-11

    rows = []
    for start in (.1, .4, .7):
        for label, arm in (("first axis", (.16, 0.)), ("second axis", (0., .16)),
                           ("diagonal", (.16/np.sqrt(2), .16/np.sqrt(2)))):
            elapsed = []
            for sign in (1, -1):
                reflected = receiver_time(start, arm, sign)
                received = receiver_time(reflected, arm, sign)
                brinkmann_check(start, reflected, (0., 0.), arm, sign)
                brinkmann_check(reflected, received, arm, (0., 0.), sign)
                elapsed.append(received-start)
            half_difference = abs(elapsed[0]-elapsed[1])/2
            if label == "diagonal":
                assert half_difference > 1e-5
            else:
                assert half_difference < 2e-13
            rows.append(dict(sent=start, arm=label, return_delays=elapsed,
                             common_error_floor=half_difference))
    return rows


def flux_reader():
    """Neutral two-path amplitude, calibrated on zero transfer; signed probe chirality."""
    rows = []
    before = 3-4
    for fraction in (.01, .125, .25, .5):
        markers = [np.array([1, np.exp(2j*np.pi*fraction*(before+2*q))])/np.sqrt(2)
                   for q in (0, 1)]
        overlap = abs(np.vdot(*markers))
        success = (1+np.sqrt(max(0., 1-min(1., overlap**2))))/2
        np.testing.assert_allclose(success, (1+abs(np.sin(2*np.pi*fraction)))/2,
                                   atol=2e-8)
        rows.append(dict(area_fraction=fraction, marker_overlap=overlap,
                         equal_prior_success=(1+abs(np.sin(2*np.pi*fraction)))/2,
                         calibrated_dark_port=float(np.sin(2*np.pi*fraction)**2)))
    return rows


def charged_passage():
    """Two- and four-component real-time spinors in a uniform outgoing flux sector.

    Time and all gaps are scaled by the square root of the scalar sweep speed.
    Reversing the field reverses the physical spin label on every Landau orbit.
    """
    sx = np.array([[0, 1], [1, 0.]])
    sz = np.diag([1., -1.])
    field, impact = .35, .6
    rows = []
    for level in range(4):
        if level == 0:
            sweep, gap, chirality = sz, impact*sx, np.eye(2)
        else:
            sweep = np.kron(sz, sz)
            gap = np.sqrt(2*field*level)*np.kron(sx, sz)+impact*np.kron(np.eye(2), sx)
            chirality = np.kron(sz, np.eye(2))
        theory = (1 if level == 0 else 2)*np.exp(-np.pi*(impact**2+2*field*level))
        approximations = []
        for endpoint in (18., 36.):
            energies, states = np.linalg.eigh(-endpoint*sweep+gap)
            filled = states[:, energies < 0].astype(complex)
            def rhs(t, y):
                return (-1j*(t*sweep+gap)@y.reshape(filled.shape)).ravel()
            end = integrate(rhs, (-endpoint, endpoint), filled.ravel()).y[:, -1].reshape(filled.shape)
            energies, states = np.linalg.eigh(endpoint*sweep+gap)
            empty = states[:, energies > 0]
            detected = empty@(empty.conj().T@end)
            total = float(np.vdot(detected, detected).real)
            signed = float(np.vdot(detected, chirality@detected).real)
            assert abs(total-theory) < 2e-4
            if level:
                assert abs(signed) < 3e-9
            approximations.append(dict(endpoint=endpoint, total=total, signed=signed))
        rows.append(dict(level=level, asymptotic=theory, finite=approximations))
    lowest = np.exp(-np.pi*impact**2)
    numbers = lowest*np.exp(-2*np.pi*field*np.arange(60))
    numbers[1:] *= 2
    work_at_36 = np.sum(2*np.sqrt(36**2+impact**2+2*field*np.arange(60))*numbers)
    speeds = np.array([.6, 1., 1.4])
    weights = np.array([.25, .50, .25])
    signed = np.exp(-np.pi*impact**2/speeds)
    total = signed/np.tanh(np.pi*field/speeds)
    mean = weights@signed
    fraction = mean/(weights@total)
    assert mean**2*(1+fraction) <= 1-fraction
    return dict(field_over_speed=field, offset_over_sqrt_speed=impact, levels=rows,
                total=lowest/np.tanh(np.pi*field), signed_at_positive_flux=lowest,
                fermion_pair_energy_asymptotic_occupations_at_36=work_at_36,
                incoherent_passages=dict(speeds=speeds.tolist(), weights=weights.tolist(),
                                         signed_per_flux=mean, polarization_fraction=fraction))


def torus_index(size, flux, distortion):
    """Index from the signature of a Wilson kernel, checked with chiral zero modes."""
    x, y = np.indices((size, size))
    links_x = np.exp(-2j*np.pi*flux*y/size**2)
    links_y = np.exp(1j*distortion*np.sin(2*np.pi*x/size))
    links_y[:, -1] *= np.exp(2j*np.pi*flux*np.arange(size)/size)
    plaquettes = links_x*np.roll(links_y, -1, axis=0)*np.roll(links_x,-1,axis=1).conj()*links_y.conj()
    phases = np.angle(plaquettes)
    np.testing.assert_allclose(phases.sum()/(2*np.pi), flux, atol=5e-12)
    if distortion == 0:
        np.testing.assert_allclose(np.prod(plaquettes[:size//2, :size//2]),
                                   np.exp(.5j*np.pi*flux), atol=3e-13)
    sites = size**2
    shifts = []
    for direction, link in enumerate((links_x, links_y)):
        shift = np.zeros((sites, sites), complex)
        neighbors = np.roll(np.arange(sites).reshape((size, size)), -1, axis=direction)
        shift[np.arange(sites), neighbors.ravel()] = link.conj().ravel()
        shifts.append(shift)
    identity = np.eye(sites)
    pauli = [np.array([[0., 1], [1, 0]]), np.array([[0., -1j], [1j, 0]]), np.diag([1., -1.])]
    wilson = identity-sum(t+t.conj().T for t in shifts)/2  # Wilson mass parameter one.
    kernel = np.kron(pauli[2], wilson)
    for spin, shift in zip(pauli[:2], shifts):
        kernel += np.kron(spin, (shift-shift.conj().T)/(2j))
    energies, basis = np.linalg.eigh(kernel)
    index = int(-np.sign(energies).sum()/2)
    sigma = np.kron(pauli[2], identity)
    overlap = sigma+(basis*np.sign(energies))@basis.conj().T
    modes, vectors = np.linalg.eigh(overlap)
    zero = vectors[:, abs(modes)<1e-9]
    signed = np.trace(zero.conj().T@sigma@zero).real
    assert index == flux and abs(signed-index) < 2e-10 and zero.shape[1] == abs(flux)
    return dict(size=size, flux=flux, distortion=distortion, index=index,
                kernel_gap=float(min(abs(energies))), zero_modes=zero.shape[1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path)
    args = parser.parse_args()
    flat_flrw = 2*quad(lambda t: (t*t-1)/(1+t*t)**2.5, -np.inf, np.inf)[0]
    np.testing.assert_allclose(flat_flrw, -4/3, atol=2e-12)
    results = dict(flat_flrw_unit_scales=flat_flrw, fifth_harmonic=cutoff_scan(), nonlinear=nonlinear_test(),
                   commuting_control=commuting_control(), shared_source=shared_source(),
                   seventh_matrix=[monodromy(.5, n)[1] for n in (1, 2, 3, 4, 6)],
                   occupied_ports=edge_absorption(), radar=radar(), flux_reader=flux_reader(),
                   charged_passage=charged_passage(),
                   torus=[torus_index(size, flux, d) for size in (8, 12)
                          for flux in (-1, 1, 3) for d in (0., .23)])
    target = Path(__file__).resolve().parents[1]/"verification"/"cat-bounce-records-results.json"
    target.write_text(json.dumps(results, indent=2, allow_nan=False)+"\n", encoding="utf8")
    if args.figure:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig, axes = plt.subplots(1, 2, figsize=(8., 3.1), constrained_layout=True)
        speeds = np.linspace(.08, .85, 100)
        axes[0].plot(speeds, [monodromy(h, 5)[1]["trace"] for h in speeds], color="#204c72")
        axes[0].axhline(-2, color="0.4", ls="--", lw=.9)
        axes[0].axvline(np.sqrt(5)/4, color="#9b392c", ls=":", lw=1.2)
        axes[0].set(xlabel="Initial rotation speed $h$", ylabel="Trace over one period")
        diagonal = [row for row in results["radar"] if row["arm"] == "diagonal"]
        for i, label in enumerate(("First wave", "Reflected polarization")):
            axes[1].plot([row["sent"] for row in diagonal],
                         [row["return_delays"][i] for row in diagonal], "o-", label=label)
        axes[1].set(xlabel="Emission clock reading", ylabel="Diagonal round-trip time")
        axes[1].legend(frameon=False, fontsize=8)
        fig.savefig(args.figure)


if __name__ == "__main__":
    main()
