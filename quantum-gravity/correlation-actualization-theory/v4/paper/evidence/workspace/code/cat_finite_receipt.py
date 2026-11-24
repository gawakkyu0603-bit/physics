"""Finite gravitational reception and a freely falling elastic sphere (volume 7, T.16)."""
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.linalg import eigh, expm, null_space
from scipy.special import log_ndtr, ndtr


G = 6.67430e-11
C_LIGHT = 299792458.
HBAR = 1.054571817e-34
BOLTZMANN = 1.380649e-23
GM_SUN = 1.3271244e20  # IAU nominal solar mass parameter in SI.
TENSOR = np.diag([1., -1., 0.])/np.sqrt(2)


def static_moments():
    """Unit radius, unit mass, lambda/rho = mu/rho = 1."""
    a, b, c = Fraction(7, 33), Fraction(-3, 22), Fraction(2, 33)
    assert -18*b-24*c == 1 and a+2*b+c == 0 and 4*b+9*c == 0
    weight = Fraction(1, 5)
    compliance = a/5+b/7+2*c/35
    inverse_square = a*a/5+2*a*b/7+b*b/9+4*a*c/35+4*b*c/45+2*c*c/45
    return float(weight), float(compliance), float(inverse_square)


def elastic_modes(cells):
    """Independent radial finite elements for the full even-parity l=2 sector.

    u = U(r) Y n + V(r) grad_S Y, where Y=n.T @ TENSOR @ n.
    All angular integrals are exact. Both radial functions are continuous
    and vanish at the center; natural boundary conditions give zero traction.
    """
    angular = 6.  # l(l+1)
    # <Y^2>_sphere=2/15 for a unit STF tensor; unit total mass gives volume weight 3 r^2.
    angular_factor = 2/5
    points, weights = leggauss(4)
    size = 2*(cells+1)
    mass = np.zeros((size, size))
    stiffness = np.zeros_like(mass)
    force = np.zeros(size)
    for cell in range(cells):
        indices = np.array([2*cell, 2*cell+1, 2*cell+2, 2*cell+3])
        for t, w in zip(points, weights):
            u = np.array([(1-t)/2, 0., (1+t)/2, 0.])
            v = np.roll(u, 1)
            du = np.array([-cells, 0., cells, 0.])
            dv = np.roll(du, 1)
            radius = (cell+(1+t)/2)/cells
            weight = angular_factor*radius**2*w/(2*cells)
            div = du+(2*u-angular*v)/radius
            mixed = dv+(u-v)/radius
            strain = np.outer(du, du)+(angular/2)*np.outer(mixed, mixed)
            strain += (2*np.outer(u, u)-angular*(np.outer(u, v)+np.outer(v, u))
                       +angular*(angular-1)*np.outer(v, v))/radius**2
            stiffness[np.ix_(indices, indices)] += weight*(np.outer(div, div)+2*strain)
            mass[np.ix_(indices, indices)] += weight*(np.outer(u, u)+angular*np.outer(v, v))
            # T x = r*(Y n + grad_S Y/2)
            force[indices] += weight*radius*(u+angular*v/2)
    values, vectors = eigh(stiffness[2:, 2:], mass[2:, 2:])
    assert values[0] > 0
    return values, (vectors.T@force[2:])**2


def radial_response(z):
    """Rational Laplace kernels of the retarded s^-2 tide, no oscillatory start-up."""
    a = quad(lambda u: u*np.exp(-u)/(1+(u/z)**2), 0, np.inf, epsabs=2e-13)[0]
    b = quad(lambda u: u*u*np.exp(-u)/(1+(u/z)**2), 0, np.inf, epsabs=2e-13)[0]
    return a, b


def even_shear(z):
    """Equal-prior comparison of a calibrated zero mean and two opposite shifts.

    The threshold here optimizes a possible material reading. It is not a CAT rate.
    """
    if z < 1e-4:
        threshold = 1+z*z/12
    else:
        threshold = z/2+np.log1p(np.sqrt(-np.expm1(-z*z)))/z
    false_tag = 2*ndtr(-threshold)
    miss = ndtr(threshold-z)-ndtr(-threshold-z)
    if z < 1e-4:
        # The advantage is quadratic. Directly subtracting the two error
        # probabilities at zero signal would lose it to round-off.
        advantage = np.exp(-.5)/np.sqrt(2*np.pi)*z*z*(1-z*z/6)
    else:
        advantage = 1-false_tag-miss
    return dict(threshold_in_noise=threshold, false_tag=false_tag, missed_tag=miss,
                success=.5+.5*advantage, advantage_over_random=.5*advantage)


def elastic_check():
    exact = np.array(static_moments())
    records = []
    for cells in (10, 20, 40, 80, 160):
        frequencies2, weights = elastic_modes(cells)
        moments = np.array([weights.sum(), (weights/frequencies2).sum(), (weights/frequencies2**2).sum()])
        rel_errors = np.abs(moments/exact-1)
        np.testing.assert_allclose(moments[0], exact[0], rtol=1e-9)
        if cells == 160:
            assert max(rel_errors) < 3.2e-5
        if records:
            assert 3.8 < records[-1]["relative_errors"][1]/rel_errors[1] < 4.1
        records.append(dict(cells=cells, first_frequency=float(np.sqrt(frequencies2[0])),
                            moments=moments.tolist(), relative_errors=rel_errors.tolist()))
    responses = []
    for time in (.1, 1., 10.):
        frequencies = np.sqrt(frequencies2)
        kernels = np.array([radial_response(time*f) for f in frequencies])
        a, b = kernels.T
        normalized = np.sum(weights*a/frequencies2)/np.sum(weights/frequencies2)
        limit = 1/(1+6*moments[2]/(moments[1]*time**2))
        quanta_scaled = .5*np.sum(weights*(a*a+(b/(frequencies*time))**2)/frequencies**3)
        lower = (moments[1]*limit)**2/(2*np.sqrt(moments[0]*moments[1]))
        upper = np.sqrt(moments[1]*moments[2])/2
        assert limit < normalized < 1 and lower < quanta_scaled < upper
        responses.append(dict(time=time, fraction=normalized, lower_fraction=limit,
                              quanta_scaled=quanta_scaled, bounds=[lower, upper]))
    # Independent Fourier sine integral of the actual causal force.
    for z in (.2, 1., 5., 25.):
        sine = quad(lambda u: 1/(1+u)**2, 0, np.inf, weight="sin", wvar=z, epsabs=2e-12)[0]
        cosine = quad(lambda u: 1/(1+u)**2, 0, np.inf, weight="cos", wvar=z, epsabs=2e-12)[0]
        a, b = radial_response(z)
        np.testing.assert_allclose([a, b], [z*sine, z*z*cosine], atol=3e-10)
    return dict(static_exact=exact.tolist(), meshes=records, causal_responses=responses)


def material_cases():
    density = 2500.  # Effective isotropic material, not a measurement of human tissue.
    shear_speed = 3000.
    specifications = [(70., (3*70/(4*np.pi*density))**(1/3)),
                      (4*np.pi*density*(5e-5)**3/3, 5e-5)]
    w0, chi0, chi20 = static_moments()
    cases = []
    for solar_masses in (10., 100., 1e6):
        horizon = 2*GM_SUN*solar_masses/C_LIGHT**2
        time_left = 2*horizon/(3*C_LIGHT)
        for mass, radius in specifications:
            inertia = 3*mass*radius**2/5
            w = w0*mass*radius**2
            chi = chi0*mass*radius**4/shear_speed**2
            chi2 = chi20*mass*radius**6/shear_speed**4
            # Two orthogonal radial directions in the material frame, equal curvature invariants.
            tide_difference = 2*np.sqrt(2)/(3*time_left**2)
            fraction = 1/(1+6*chi2/(chi*time_left**2))
            mean_floor = tide_difference*chi*fraction
            max_vacuum_variance = HBAR*np.sqrt(w*chi)/2
            n_min = mean_floor**2/(4*max_vacuum_variance)
            n_max = tide_difference**2*np.sqrt(chi*chi2)/(2*HBAR)
            assert 0<n_min<=n_max
            temperature_results = []
            for temperature in (0., .01, 300.):
                variance = max_vacuum_variance+BOLTZMANN*temperature*chi
                z = mean_floor/(2*np.sqrt(variance))
                exponent = n_max if temperature == 0 else min(n_max,tide_difference**2*chi/(4*BOLTZMANN*temperature))
                optimum_upper = (1+np.sqrt(-np.expm1(-exponent)))/2
                assert ndtr(z) <= optimum_upper+1e-15
                temperature_results.append(dict(kelvin=temperature, midpoint_z=z,
                                                success_lower=float(ndtr(z)), log_error_upper=float(log_ndtr(-z)),
                                                all_readouts_upper=optimum_upper, fidelity_exponent_upper=exponent,
                                                sign_blind_at_minimum_z=even_shear(z)))
            # This is a separate short, high carrier frequency radiative benchmark.
            # The angular-frequency cutoff obeys Omega times the window = 100.
            window = horizon/C_LIGHT
            omega = 100/window
            depth = 4*G*inertia*omega**4*window/(3*C_LIGHT**5)
            cases.append(dict(solar_masses=solar_masses, mass_kg=mass, radius_m=radius,
                              proper_time_left_s=time_left, sound_time_ratio=radius/(shear_speed*time_left),
                              load_parameter=tide_difference*radius**2/shear_speed**2,
                              fraction_lower=fraction, quanta_interval=[n_min, n_max],
                              thermal=temperature_results, radiation_depth_upper=depth,
                              wavelength_parameter=omega*radius/C_LIGHT))
    return cases


def causal_network():
    """Complete passive unitary collisions with noncommuting bright directions and two input modes per bin."""
    rng = np.random.default_rng(167)
    dim, bins, channels = 4, 15, 2
    radiation = bins*channels
    joint = np.eye(dim+radiation, dtype=complex)
    contraction = np.eye(dim, dtype=complex)
    floor = 1.
    for n in range(bins):
        coupling = (rng.normal(size=(dim, channels))+1j*rng.normal(size=(dim, channels)))*.09
        generator = np.block([[np.zeros((dim, dim)), coupling], [-coupling.conj().T, np.zeros((channels, channels))]])
        beam = expm(generator)
        turn = expm(1j*np.diag(rng.normal(0, .1, dim)))
        beam[:dim] = turn@beam[:dim]
        block = beam[:dim, :dim]
        floor *= np.linalg.svd(block, compute_uv=False)[-1]**2
        contraction = block@contraction
        ix = np.r_[np.arange(dim), dim+channels*n+np.arange(channels)]
        joint[ix] = beam@joint[ix]
    np.testing.assert_allclose(joint.conj().T@joint, np.eye(len(joint)), atol=2e-14)
    transfer, output = joint[:dim, dim:], joint[dim:, dim:]
    np.testing.assert_allclose(joint[:dim,:dim], contraction, atol=2e-14)
    values = np.linalg.svd(transfer, compute_uv=False)
    np.testing.assert_allclose(1-values[0]**2, np.linalg.svd(output, compute_uv=False)[-1]**2)
    assert 1-values[0]**2 >= floor-1e-13
    # One physical dark input and an optimally matched input, both without a vacuum component.
    dark = null_space(transfer)[:, 0]
    np.testing.assert_allclose(np.linalg.norm(output@dark), 1., atol=2e-14)
    matched = np.linalg.svd(transfer, full_matrices=False)[2][0].conj()
    successful = np.linalg.norm(transfer@matched)**2
    return dict(bins=bins, material_dimension=dim, matched_capture=successful, no_capture_floor=floor,
                three_matched_quanta_miss=(1-successful)**3,
                coherent_mean_three_miss=np.exp(-3*successful))


def charge_and_recovery():
    """Symmetric coarse charge projections preserve an unknown orientation code."""
    shear = np.linspace(-12., 12., 1001)
    parity = np.arange(len(shear))[::-1]
    # Bolt the loading axes to the two retained, orthogonal material reference states.
    g = np.exp(-(shear-3)**2/4)
    g /= np.linalg.norm(g)
    h = g[parity]
    records = {}
    for name, groups in [("even", [np.abs(shear)>1.5, np.abs(shear)<=1.5]),
                         ("signed", [shear>1.5, shear < -1.5, np.abs(shear)<=1.5])]:
        # The grids are constructed with exactly corresponding reflected index sets.
        if name == "even":
            groups[0] = groups[0] | groups[0][parity]
            groups[1] = ~groups[0]
        else:
            groups[1] = groups[0][parity]
            groups[2] = ~(groups[0] | groups[1])
        weights = np.array([[np.vdot(v[mask], v[mask]).real for v in (g,h)] for mask in groups])
        np.testing.assert_allclose(weights.sum(axis=0), np.ones(2))
        fidelity = (1+np.sqrt(weights.prod(axis=1)).sum())/2
        if name == "even":
            np.testing.assert_allclose(weights[:,0], weights[:,1], atol=1e-14)
            np.testing.assert_allclose(fidelity, 1., atol=1e-14)
        else:
            assert fidelity < .56
        records[name] = dict(weights=weights.tolist(), ideal_entanglement_fidelity=fidelity)
    return records


if __name__ == "__main__":
    result = dict(elastic=elastic_check(), physical_cases=material_cases(), network=causal_network(),
                  charge_recovery=charge_and_recovery())
    destination = Path(__file__).resolve().parents[1]/"verification"/"cat-finite-receipt-results.json"
    destination.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
