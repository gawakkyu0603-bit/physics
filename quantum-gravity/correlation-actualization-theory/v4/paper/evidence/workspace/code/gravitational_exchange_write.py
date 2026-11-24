"""Compare angular scattering and a private record with the same reduced dynamics.

The zero of the angle variable x = sin(theta/2)^2 is taken after forming an
information difference. Counting every Newtonian deflection has no such limit.
"""
import math

import numpy as np
from scipy.integrate import quad


def exchange_write_checks():
    rng = np.random.default_rng(19473)
    rows = []
    for dim in (2, 3, 5):
        eye = np.eye(dim**2)
        swap = eye.reshape(dim, dim, dim, dim).transpose(1, 0, 2, 3).reshape(eye.shape)
        odd = (eye-swap)/2
        even = eye-odd

        def state(n):
            a = rng.normal(size=(n, n))+1j*rng.normal(size=(n, n))
            positive = a @ a.conj().T
            return positive/np.trace(positive)

        def dissipator(jump, rho):
            rate = jump.conj().T @ jump
            return jump @ rho @ jump.conj().T-(rate @ rho+rho @ rate)/2

        rho, sa, sb = state(dim**2), state(dim), state(dim)
        joint = np.kron(sa, sb)
        direct, exchange = 2.37+.41j, -.68+.33j
        jump = direct*eye+exchange*swap
        drift = 1j*(direct.conjugate()*exchange).imag*(swap @ rho-rho @ swap)
        delta = dissipator(jump, rho)-dissipator(2*exchange*odd, rho)-drift
        channel_error = np.linalg.norm(delta)
        opacity = .73
        survival = math.exp(-opacity/2)
        quiet = even+survival*odd
        mark = math.sqrt(1-survival**2)*odd
        whole = quiet @ rho @ quiet+mark @ rho @ mark
        reference = even @ rho @ even+odd @ rho @ odd+survival*(even @ rho @ odd+odd @ rho @ even)
        assert np.linalg.norm(quiet @ quiet+mark @ mark-eye) < 3e-15
        assert np.linalg.norm(whole-reference) < 4e-15
        odd_prob = lambda a, b: np.trace(odd @ np.kron(a, b)).real
        mixed_difference = 2*odd_prob(sa, sb)-odd_prob(sa, sa)-odd_prob(sb, sb)
        target = np.linalg.norm(sa-sb)**2/2
        assert abs(mixed_difference-target) < 2e-15 and channel_error < 5e-15
        assert abs(np.trace(mark @ joint @ mark).real-(1-math.exp(-opacity))*odd_prob(sa, sb)) < 1e-15
        # A gravity-generated outgoing reference and its orthogonal complement.
        g_even = np.array([1., 0.])
        g_odd = np.array([survival, math.sqrt(1-survival**2)])
        isometry = np.kron(g_even[:, None], even)+np.kron(g_odd[:, None], odd)
        assert np.linalg.norm(isometry.conj().T @ isometry-eye) < 1e-15
        rows.append(dict(internal_dimension=dim, channel_residual=float(channel_error),
                         mixed_calibration=float(mixed_difference), hilbert_schmidt_half=float(target)))
    # All areas in units of A^2, where A = G m^2/(2 mu_orb v^2).
    finite_exchange = 4*math.pi*quad(lambda x: (1-x)**-2, 0, .5)[0]
    assert abs(finite_exchange-4*math.pi) < 2e-14
    areas = []
    for epsilon in (1., .3, .01, .0001):
        def stable_area(x):
            # Rationalization retains the leading epsilon^2 without subtracting large fluxes.
            return 2*epsilon**2/(1+math.sqrt(1-2*epsilon*x*(1-x)))**2
        h = 4*math.pi*quad(stable_area, 0, .5, epsabs=1e-24)[0]
        # Independently integrate the actual two angular amplitudes on a finite aperture.
        xmin = .002
        def raw_difference(x):
            d, e = 1/x, 1/(1-x)
            same = d+e
            different = math.sqrt(d*d+e*e+2*(1-epsilon)*d*e)
            return (same-different)**2/2
        finite = 4*math.pi*quad(raw_difference, xmin, .5, epsabs=1e-18)[0]
        aperture = 4*math.pi*quad(stable_area, xmin, .5, epsabs=1e-24)[0]
        assert abs(finite/aperture-1) < 3e-9
        assert math.pi*(1-2e-14) <= h/epsilon**2 <= 4*math.pi/(1+math.sqrt(1-epsilon/2))**2+2e-14
        areas.append(dict(mismatch=epsilon, area=h, area_over_mismatch_squared=h/epsilon**2))
    assert abs(areas[-1]['area_over_mismatch_squared']/math.pi-1) < 2e-5
    return dict(exchange_area=finite_exchange, initial_dark_rate_per_mismatch=2*finite_exchange,
                angular_results=areas, density_matrix_checks=rows)
