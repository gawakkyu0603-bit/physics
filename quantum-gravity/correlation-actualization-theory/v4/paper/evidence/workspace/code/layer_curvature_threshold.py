"""Curvature-triggered gravity on a GR fluid star and direct inter-layer couplings.

Lengths are measured in the stellar radius. The fluid is held on the exact
incompressible GR background during the linear onset calculation. We count
only the positive-curvature, lowest, nodeless mode of a massless scalar.
"""
import math

import numpy as np
from numpy.polynomial.legendre import Legendre, leggauss
from scipy.integrate import solve_ivp
from scipy.linalg import eigh
from scipy.optimize import brentq


def stellar_profile(x, compactness):
    surface = np.sqrt(1-2*compactness)
    radial = np.sqrt(1-2*compactness*x*x)
    lapse = (3*surface-radial)/2
    pressure_ratio = (radial-surface)/(3*surface-radial)
    ricci = 6*compactness*(1-3*pressure_ratio)
    return radial, lapse, ricci


def critical_coupling(compactness, partner_strength=0.):
    surface_cost = -2*compactness/math.log1p(-2*compactness)
    points, weights = leggauss(96)
    radii = (points+1)/2
    radial, lapse, ricci = stellar_profile(radii, compactness)
    assert np.min(ricci) > 0
    polynomials = [Legendre.basis(n) for n in range(9)]
    basis = np.array([p(2*radii**2-1) for p in polynomials])
    slopes = np.array([4*radii*p.deriv()(2*radii**2-1) for p in polynomials])
    stiffness = (slopes*(weights*radii**2*radial*lapse/2)) @ slopes.T
    stiffness += surface_cost*np.ones_like(stiffness)  # each basis value at x=1 is one
    curvature = (basis*(weights*radii**2*lapse*ricci/(2*radial))) @ basis.T
    # A mean-zero partner with equal signs has rms profile (1-x²)^3.
    load = (basis*(weights*radii**2*lapse*(1-radii**2)**6/(2*radial))) @ basis.T
    eigenvalues, modes = eigh(stiffness-partner_strength*load, curvature, subset_by_index=(0, 0))
    variational = float(eigenvalues[0])
    mode = modes[:, 0]
    partner_slope = float(-(mode @ load @ mode)/(mode @ curvature @ mode))
    start = 1e-6
    _, central_lapse, central_ricci = stellar_profile(0., compactness)

    def shoot(coupling, inspect=False):
        def equation(x, state):
            b, a, scalar_curvature = stellar_profile(x, compactness)
            field, flux = state
            effective_curvature = coupling*scalar_curvature+partner_strength*(1-x*x)**6
            return (flux/(x*x*a*b), -x*x*(a/b)*effective_curvature*field)

        central_potential = coupling*central_ricci+partner_strength
        init = [1-central_potential*start**2/6,
                -central_potential*central_lapse*start**3/3]
        sol = solve_ivp(equation, (start, 1.), init, method="DOP853", rtol=3e-12, atol=1e-13)
        assert sol.success
        field, flux = sol.y[:, -1]
        if inspect:
            assert sol.y[0].min() > 0
        return flux+surface_cost*field

    critical = brentq(shoot, 0., 1.02*variational, xtol=1e-12, rtol=3e-14)
    assert abs(shoot(critical, inspect=True)) < 3e-10
    assert abs(critical/variational-1) < 2e-9
    return dict(compactness=compactness, critical_xi=critical, rayleigh_ritz=variational,
                scaled_threshold=compactness*critical, newtonian_scaled_limit=math.pi**2/24,
                partner_strength=partner_strength, derivative_wrt_partner=partner_slope)


def irreversible_contact():
    """Trace the partner out after exact completely positive Markov evolution."""
    exposure = math.log(2)/8
    states = []
    for spectrum, weights in (([-1., 1.], [.5, .5]),
                              ([-math.sqrt(2), 0., math.sqrt(2)], [.25, .5, .25])):
        y = np.array(spectrum)
        weights = np.array(weights)
        assert abs(weights @ y) < 1e-13 and abs(weights @ (y*y)-1) < 1e-13
        pair = np.kron(np.ones((2, 2))/2, np.diag(weights))
        retained = []
        for power in (1, 2):
            levels = ((np.array([1., -1.])[:, None]-y[None, :])**power).ravel()
            kernel = np.exp(-exposure*(levels[:, None]-levels[None, :])**2/2)
            after = pair*kernel
            assert np.linalg.eigvalsh(kernel).min() > -2e-14
            assert abs(np.trace(after)-1) < 1e-14
            local = np.trace(after.reshape(2, len(y), 2, len(y)), axis1=1, axis2=3)
            retained.append(float(2*local[0, 1]))
        states.append(retained)
    assert abs(states[0][0]-states[1][0]) < 1e-14
    assert abs(states[0][1]-.5) < 1e-14 and abs(states[1][1]-.625) < 1e-14
    return dict(exposure=exposure, linear_contact=[s[0] for s in states],
                squared_contact=[s[1] for s in states],
                eliminated_rate_gap=states[1][1]-states[0][1])


def bounded_phase_contact():
    """Compare two Hermitian marks with correlated local unitary kicks."""
    x = np.array([-1.2, .1, 1.4])
    y = np.array([-.4, .8])
    k = .73
    phases = k*(x[:, None]-y[None, :]).ravel()
    cosine, sine = np.diag(np.cos(phases)), np.diag(np.sin(phases))
    kick = np.kron(np.diag(np.exp(1j*k*x)), np.diag(np.exp(-1j*k*y)))
    rng = np.random.default_rng(271828)
    samples = rng.normal(size=(6, 4)) + 1j*rng.normal(size=(6, 4))
    joint = samples @ samples.conj().T
    joint /= np.trace(joint)

    def dissipator(mark):
        square = mark @ mark
        return mark @ joint @ mark-(square @ joint+joint @ square)/2

    def random_kick(state, unitary):
        return (unitary @ state @ unitary.conj().T +
                unitary.conj().T @ state @ unitary)/2-state

    generator = dissipator(cosine)+dissipator(sine)
    kick_error = np.max(abs(generator-random_kick(joint, kick)))
    joint_blocks = joint.reshape(3, 2, 3, 2)
    derivative_blocks = generator.reshape(3, 2, 3, 2)
    local_errors = []
    local_specs = [(1, 3, x, k), (0, 2, y, -k)]
    for axis1, axis2, spectrum, sign_k in local_specs:
        marginal = np.trace(joint_blocks, axis1=axis1, axis2=axis2)
        reduced_derivative = np.trace(derivative_blocks, axis1=axis1, axis2=axis2)
        local_kick = np.diag(np.exp(1j*sign_k*spectrum))
        local_errors.append(float(np.max(abs(reduced_derivative-random_kick(marginal, local_kick)))))
    assert max(kick_error, *local_errors) < 2e-15
    return dict(seed=271828, dimension=[3, 2], kick_identity_error=float(kick_error),
                marginal_generator_errors=local_errors)


def contact_force_balance():
    """Displace one identification map at a time and differentiate the full action."""
    nodes, weights = leggauss(100)
    z, weights = (nodes+1)/2, weights/2
    shift = z**2*(1-z)**2
    shift_gradient = 2*z*(1-z)*(1-2*z)
    strength = .82

    def volume(chart, layer):
        return (1+.2*chart)/2 if layer == 0 else (1+.45*chart**2)/2

    def scalar(chart, layer):
        return .35+.23*chart**2 if layer == 0 else (1-chart**2)**3

    def action(displacement, moved):
        charts = [z, z]
        charts[moved] = z+displacement*shift
        densities = [volume(chart, layer) for layer, chart in enumerate(charts)]
        densities[moved] *= 1+displacement*shift_gradient
        a, b = (scalar(chart, layer) for layer, chart in enumerate(charts))
        potential = strength*(a*a-b*b)**2/8
        return -float(weights @ ((densities[0]+densities[1])*potential))

    a, b = scalar(z, 0), scalar(z, 1)
    densities = [volume(z, 0), volume(z, 1)]
    derivatives = [strength*(a*a-b*b)*a*(.46*z)/2,
                   -strength*(a*a-b*b)*b*(-6*z*(1-z*z)**2)/2]
    total_volume = sum(densities)
    forces = [density*sum(derivatives)-total_volume*change
              for density, change in zip(densities, derivatives)]
    analytic = [float(weights @ (force*shift)) for force in forces]
    step = 2e-5
    finite = [(action(step, layer)-action(-step, layer))/(2*step) for layer in (0, 1)]
    residual = float(np.max(abs(forces[0]+forces[1])))
    assert max(abs(np.array(finite)-analytic)) < 2e-10 and residual < 4e-16
    assert analytic[0]*analytic[1] < 0
    # Per total density, for equal layer volumes, a zero probe, and unit scales.
    x = .5
    partner = (1-x*x)**3
    bare_force = partner**3*(-6*x*(1-x*x)**2)/4
    assert bare_force < 0
    return dict(force_from_variation=finite, integrated_force=analytic,
                largest_pointwise_imbalance=residual, unbalanced_zero_probe_at_half_radius=bare_force)


def curvature_action_checks():
    stars = [critical_coupling(c) for c in (.0005, .05, .15, .2, .25)]
    assert abs(stars[0]["scaled_threshold"]-math.pi**2/24) < .0003
    loaded = [critical_coupling(.2, amplitude) for amplitude in (.002, .004, 1.)]
    unloaded = next(star for star in stars if star["compactness"] == .2)
    f0 = unloaded["critical_xi"]
    finite_slope = (-3*f0+4*loaded[0]["critical_xi"]-loaded[1]["critical_xi"])/.004
    assert abs(finite_slope-unloaded["derivative_wrt_partner"]) < 5e-8
    assert 0 < loaded[-1]["critical_xi"] < f0
    cones = []
    for contrast in (.025, .1, -.3):
        principal = np.array([[1., contrast], [contrast, 1+contrast**2]])
        speeds = np.sqrt(np.linalg.eigvalsh(principal))
        expected = np.sqrt(1+contrast**2/4)+np.array([-1, 1])*abs(contrast)/2
        assert np.max(abs(speeds-expected)) < 1e-14
        assert speeds[0] < 1 < speeds[1]
        cones.append(dict(curvature_contrast=contrast, slow=speeds[0], fast=speeds[1]))
    # Opposite scalar signs leave an even gravitational charge indistinguishable.
    s, perturbation, strength = .7, .11, .9
    direct = strength*((s+perturbation)**2-(s-perturbation)**2)**2/8
    assert math.isclose(direct, 2*strength*s**2*perturbation**2)
    return dict(stars=stars, loaded_stars=loaded, baseline_slope_from_shooting=finite_slope,
                angular_characteristics=cones, direct_pair_energy=direct,
                irreversible_contact=irreversible_contact(), bounded_phase_contact=bounded_phase_contact(),
                contact_force_balance=contact_force_balance())
