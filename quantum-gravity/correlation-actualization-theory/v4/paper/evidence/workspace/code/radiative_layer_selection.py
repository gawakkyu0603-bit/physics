"""Gravity carried away from a scattering body and gravity absorbed by its own matter.

Angles refer to unordered outgoing axes. Graviton polarizations have unit norm.
The frequency integral treats a sharp spectral resolution; it is not an exact
restriction of a null field algebra to a finite interval of retarded time.
"""
import math

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad
from scipy.linalg import eigvalsh
from scipy.special import eval_legendre, lpmv


def sphere_grid(nz=24, nphi=48):
    z, weights = leggauss(nz)
    azimuth = 2*math.pi*np.arange(nphi)/nphi
    cosine, phi = np.meshgrid(z, azimuth, indexing="ij")
    sine = np.sqrt(1-cosine**2)
    n = np.stack([sine*np.cos(phi), sine*np.sin(phi), cosine], axis=-1).reshape(-1, 3)
    measure = np.repeat(weights/(2*nphi), nphi)
    return n, measure


def transverse_power(current, directions):
    dim = directions.shape[-1]
    screen = np.eye(dim)-directions[:, :, None]*directions[:, None, :]
    trans = screen @ current @ screen
    return np.sum(trans**2, axis=(1, 2))-np.trace(trans, axis1=1, axis2=2)**2/(dim-1)


def polarization_checks():
    n, weight = sphere_grid()
    first = np.array([5., 0., 12.])/13
    second = np.array([-12., 0., 5.])/13
    a, b = np.outer(first, first), np.outer(second, second)
    current = a-b
    quadrupole_norm = np.sum(current**2)
    spectrum = []
    for beta in (0., .05, .2, .5):
        exact = (a[None, :, :]/(1-beta**2*(n@first)**2)[:, None, None]-
                 b[None, :, :]/(1-beta**2*(n@second)**2)[:, None, None])
        norm = weight @ transverse_power(exact, n)
        # The helicity basis is independent of the projected-tensor implementation.
        transverse = np.stack([-n[:, 1], n[:, 0], np.zeros(len(n))], axis=1)
        transverse /= np.linalg.norm(transverse, axis=1)[:, None]
        other = np.cross(n, transverse)
        eplus = (transverse[:, :, None]*transverse[:, None, :]-
                 other[:, :, None]*other[:, None, :])/math.sqrt(2)
        ecross = (transverse[:, :, None]*other[:, None, :]+
                  other[:, :, None]*transverse[:, None, :])/math.sqrt(2)
        basis_norm = weight @ (np.sum(exact*eplus, axis=(1, 2))**2+
                               np.sum(exact*ecross, axis=(1, 2))**2)
        assert abs(norm-basis_norm) < 2e-14
        spectrum.append(dict(speed=beta, polarization_mean=float(norm)))
    assert abs(spectrum[0]["polarization_mean"]/quadrupole_norm-2/5) < 2e-14
    current4 = np.zeros((4, 4))
    current4[:3, :3] = current
    for compact in (0., .2, .71, 1.):
        directions = np.column_stack((n*math.sqrt(1-compact**2), np.full(len(n), compact)))
        rem = 1-compact**2
        expected = 1-2*rem/3+4*rem**2/45
        assert abs(weight @ transverse_power(current4, directions)/quadrupole_norm-expected) < 2e-14
    return spectrum


def kk_weight(u):
    if abs(u) >= 1.:
        return 0.
    s = math.sqrt(1-u*u)
    return s*(1-2*s*s/3+4*s**4/45)


def kk_primitive(end_ratio):
    """Integral of W(n/(R omega)) d omega/omega from its nonzero-mode threshold."""
    x = np.maximum(end_ratio, 1.)
    s = np.sqrt(1-x**-2)
    return (19/45)*(np.arccosh(x)-s)+(26/135)*s**3-(4/225)*s**5


def compact_exponent(radius, upper, log_time_over_radius):
    # The zero mode is evaluated logarithmically even for exponentially large T.
    high = radius*upper
    low = math.exp(-log_time_over_radius)
    assert 0 <= low < high
    modes = np.arange(1, math.floor(high)+1, dtype=float)
    nonzero = np.sum(kk_primitive(high/modes)-kk_primitive(low/modes))
    zero = kk_weight(0.)*(math.log(high)+log_time_over_radius)
    return float((zero+2*nonzero)/(2*math.pi*radius))


def circle_checks():
    integral = quad(kk_weight, -1., 1., epsabs=2e-14, epsrel=2e-14)[0]
    assert abs(integral-5*math.pi/18) < 8e-15
    for radius, upper, start in ((2.7, 1., .06), (4.3, 1.2, .38), (.4, 1., .03)):
        band_edges = [n/radius for n in range(1, math.floor(radius*upper)+1)
                      if start < n/radius < upper]
        def frequency(omega):
            nmax = math.floor(radius*omega)
            return sum(kk_weight(n/(radius*omega)) for n in range(-nmax, nmax+1))/omega
        direct = quad(frequency, start, upper, points=band_edges, epsabs=2e-11)[0]/(2*math.pi*radius)
        assert abs(direct-compact_exponent(radius, upper, -math.log(start*radius))) < 2e-12
    rows = []
    for z in (0., .4, 2.):
        limit = 5/36+19*z/(90*math.pi)
        curve = [compact_exponent(r, 1., z*r) for r in (2, 8, 32, 128, 512, 2048)]
        assert abs(curve[-1]-limit) < 1e-4
        rows.append(dict(scaling=z, radii=[2, 8, 32, 128, 512, 2048], exponent=curve, limit=limit))
    return rows


def projective_kernel_checks():
    h = 1.3
    modes = []
    for half_degree in range(6):
        degree = 2*half_degree
        numeric = quad(lambda x: math.exp(-h*(1-x*x))*eval_legendre(degree, x),
                       0., 1., epsabs=4e-14)[0]
        series = 0.
        for k in range(half_degree, 42):
            moment = math.factorial(2*k)/(math.prod(range(2, 2*k-degree+1, 2))*
                                          math.prod(range(1, 2*k+degree+2, 2)))
            series += h**k/math.factorial(k)*moment
        series *= math.exp(-h)
        assert series > 0 and abs(series-numeric) < 2e-15
        modes.append(dict(degree=degree, eigenvalue=series))
    return modes


def fidelity_loss(odd_weight, missing):
    """Squared Uhlmann fidelity deficit, without cancellation for small weights."""
    b = 120/169
    d = 119/169
    q, delta = odd_weight, missing  # delta = 1-visibility^2
    v2 = 1-delta
    if q == 0:
        return 0.
    end_det4 = delta+2*q*(1-b)*v2-q*q*((1-b)**2*v2+d*d)
    denominator = 2*(delta+q*(1-b)*v2+math.sqrt(max(delta*end_det4, 0.)))
    return q*q*((1-b)**2*v2+delta*d*d)/denominator


def aperture_checks():
    b, d = 120/169, 119/169
    rows = []
    for v in (0., .5, .9, .99, 1.):
        even = np.array([[1., v], [v, 1.]])/2
        odd = np.array([[144., 60*v], [60*v, 25.]])/169
        delta = 1-v*v
        if v < 1:
            peak = (1-b*v*v+math.sqrt((1-b*v*v)**2-b*b*delta**2))/delta
            numeric = eigvalsh(odd, even)[-1]
            assert abs(peak/numeric-1) < 2e-13
        else:
            peak = None
        eps = .12
        q = eps/(4-eps)
        mixed = (1-q)*even+q*odd
        full = np.trace(even @ mixed)+2*math.sqrt(max(0., np.linalg.det(even)*np.linalg.det(mixed)))
        assert abs(fidelity_loss(q, delta)-(1-full)) < 1.5e-15
        rows.append(dict(visibility=v, max_likelihood=peak, even_dark=(1-v)/2, odd_dark=(1-b*v)/2))
    curves = []
    # T is measured in units with B=1 for the schematic short-time material input.
    times = np.geomspace(.015, .52, 65)
    for missing in (0., 1e-4, .3):
        losses = [fidelity_loss(t**6/(4-t**6), missing) for t in times]
        slope = math.log(losses[1]/losses[0])/math.log(times[1]/times[0])
        assert abs(slope-(6 if missing == 0 else 12)) < 4e-7
        curves.append(dict(missing=missing, times=times.tolist(), losses=losses, initial_slope=slope))
    return rows, curves


def harmonics(j, n):
    azimuth = np.arctan2(n[:, 1], n[:, 0])
    positive = []
    for m in range(j+1):
        norm = math.sqrt((2*j+1)*math.factorial(j-m)/(4*math.pi*math.factorial(j+m)))
        positive.append(norm*lpmv(m, j, n[:, 2])*np.exp(1j*m*azimuth))
    return np.column_stack([(-1)**abs(m)*positive[abs(m)].conj() if m < 0 else positive[m]
                            for m in range(-j, j+1)])


def rotor_tensor(source, target):
    n, weights = sphere_grid(14, 32)
    tensor = n[:, :, None]*n[:, None, :]-np.eye(3)/3
    amplitudes = 4*math.pi*np.einsum("x,xf,xij,xs->fsij", weights,
                                     harmonics(target, n).conj(), tensor, harmonics(source, n))
    width_by_m = np.sum(abs(amplitudes)**2, axis=(0, 2, 3))
    assert np.ptp(width_by_m) < 2e-15
    return float(np.mean(width_by_m))


def material_checks():
    g, c, h, kb = 6.67430e-11, 299792458., 6.62607015e-34, 1.380649e-23
    hbar = h/(2*math.pi)
    # A circular material amplitude and a helicity-resolved field expose the Wightman index order.
    material = np.array([1., 1j])/math.sqrt(2)
    emitted = np.array([1., 1j])/math.sqrt(2)
    field_spectrum = np.outer(emitted.conj(), emitted)
    assert abs(np.vdot(material, field_spectrum @ material)-abs(material @ emitted)**2) < 1e-14
    assert abs(np.vdot(material, field_spectrum.T @ material)-1.) < 1e-14
    a31, a20 = rotor_tensor(3, 1), rotor_tensor(2, 0)
    assert abs(a31-6/35) < 2e-15 and abs(a20-2/15) < 2e-15
    assert rotor_tensor(2, 1) < 3e-29 and rotor_tensor(3, 0) < 3e-29
    wavenumber = 297.5  # cm^-1, rounded molecular D2 S0(1) spectroscopic input
    omega = 2*math.pi*c*100*wavenumber
    inertia = 5*hbar/omega
    rate = 2*g*omega**5*inertia**2*a31/(5*hbar*c**5)
    assert abs(rate/(12*g*hbar*omega**3/(7*c**5))-1) < 2e-14
    temperature = hbar*omega/(kb*math.log(7/3))
    distance = c*math.log(7/3)/(2*math.pi*omega)
    mass = 6.69e-27
    # Exact kinematics in units of the lower rest mass, avoiding a mass-shell subtraction.
    eps_mass = hbar*omega/(mass*c*c)
    rest_frequency = omega/(2*math.pi)
    emitted = rest_frequency*(1+eps_mass/2)/(1+eps_mass)
    absorbed = rest_frequency*(1+eps_mass/2)
    gap = rest_frequency*eps_mass*(1+eps_mass/2)/(1+eps_mass)
    assert abs((absorbed-emitted)/gap-1) < 3e-5
    photon_width = 3.5698e-11  # Kassi et al., Table 2, v=0, S(1) electric quadrupole Einstein A
    gravity_fraction = rate/(photon_width+rate)
    assert 2.45e-35 < gravity_fraction < 2.46e-35
    rates = []
    for factor in (.5, 1., 2.):
        ratio = 7/3*math.exp(-hbar*omega/(kb*temperature*factor))
        rates.append(dict(temperature_over_balance=factor, upward_over_downward=ratio))
    assert abs(rates[1]["upward_over_downward"]-1) < 2e-15
    return dict(rotor_strength31=a31, rotor_strength20=a20, rigid_rate_ratio=(a31/a20)*(5/3)**5,
                wavenumber_cm=wavenumber, angular_frequency=omega, vacuum_rate_s=rate, electric_width_s=photon_width, gravity_branch=gravity_fraction,
                balance_temperature_K=temperature, near_horizon_distance_m=distance,
                opposite_recoil_gap_Hz=gap, speed_for_matching_m_s=c*eps_mass,
                thermal_examples=rates)


def radiative_checks():
    ports, curves = aperture_checks()
    return dict(polarization=polarization_checks(), circle=circle_checks(),
                even_harmonics=projective_kernel_checks(), orbit=ports, visibility_curves=curves,
                molecule=material_checks())
