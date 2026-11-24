"""Tidal work in a freely falling, homogeneous, traction-free elastic sphere.

All lengths and material constants in SI. Numerical checks use a second root grid,
a separate Fourier quadrature and two continuum sum rules. No random draws.
"""
import argparse
import json
import math
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import i0e, roots_laguerre, roots_legendre, spherical_jn

LIGHT = 299792458.
HBAR = 6.62607015e-34 / (2 * math.pi)
BOLTZMANN = 1.380649e-23
NEWTON = 6.67430e-11
SOLAR_GM = 1.3271244e20
DENSITY = 2200.
SHEAR = 31.e9
BULK = 35.9e9
LAME = BULK - 2 * SHEAR / 3
RATIO = LAME / SHEAR
SHEAR_SPEED = math.sqrt(SHEAR / DENSITY)
SPEED_RATIO = 1 / math.sqrt(RATIO + 2)
RADIUS = 5.e-5
TEMP = 300.
NORM_COMPLIANCE = (35 * RATIO + 26) / (70 * (19 * RATIO + 14))


def basis(s, r):
    """Radial and tangential displacement and radial derivatives for the two Lamb potentials."""
    p = SPEED_RATIO * s
    x, y = p*r, s*r
    jx, jy = spherical_jn(2, x), spherical_jn(2, y)
    dx, dy = spherical_jn(2, x, True), spherical_jn(2, y, True)
    ddx = (6 / x**2 - 1)*jx - 2*dx/x
    ddy = (6 / y**2 - 1)*jy - 2*dy/y
    return ((p*dx, jx/r, p*p*ddx, (p*dx - jx/r)/r),
            (6*jy/r, jy/r+s*dy, 6*(s*dy-jy/r)/r, (s*dy-jy/r)/r+s*s*ddy))


def traction(s):
    columns = []
    for u, v, du, dv in basis(s, 1.):
        columns.append((RATIO*(du + 2*u - 6*v) + 2*du, dv + u-v))
    return np.array(columns).T


def roots(step, limit):
    grid = np.arange(0.3, limit+step, step)
    determinant = lambda s: np.linalg.det(traction(s))
    values = [determinant(s) for s in grid]
    return [brentq(determinant, lo, hi, xtol=2e-13)
            for lo, hi, a, b in zip(grid, grid[1:], values, values[1:]) if a*b < 0]


def mode_weight(s, nquad):
    nodes, weights = roots_legendre(nquad)
    r, dr = (1+nodes)/2, weights/2
    coeff = np.linalg.svd(traction(s))[2][-1]
    left, right = basis(s, r)
    u, v = [coeff[0]*left[i]+coeff[1]*right[i] for i in (0, 1)]
    force = np.dot(dr, r**3*(u+3*v))
    mass = np.dot(dr, r*r*(u*u+6*v*v))
    return float((2/5)*force**2/mass)


@lru_cache(None)
def laguerre(order):
    return roots_laguerre(order)


def response(z, order=80):
    """Dimensionless transform of the tidal ramp, including held static shift separately."""
    nodes, weights = laguerre(order)
    return np.dot(weights, nodes**2/(nodes+1j*z))


def response_fourier(z):
    f = lambda u: 2/(1+u)**3
    return complex(quad(f, 0, np.inf, weight='cos', wvar=z, epsabs=2e-13)[0],
                   -quad(f, 0, np.inf, weight='sin', wvar=z, epsabs=2e-13)[0])


def neutral_probability(a, occupation):
    bessel_arg = 2*a*math.sqrt(occupation*(occupation+1))
    return float(i0e(bessel_arg)*math.exp(-a/(math.sqrt(occupation+1)+math.sqrt(occupation))**2))


def matched_noise_probabilities(a, occupation):
    """Zero signed work and equality of two independent reads with extra diffusion v=a."""
    mean_factor = 2*occupation + 1
    scale = math.sqrt(1 + a*mean_factor)

    def integrand(y, collision):
        den = scale**2 + y*y
        h = complex(-2*mean_factor*y*y/den, 2*scale*y/den)
        z = np.exp(a*h/(1-a*h))/(1-a*h)
        value = abs(z)**2 if collision else z.real
        return value * (2*scale/math.pi) / den

    def integrate(collision):
        return float(quad(integrand, 0, np.inf, args=(collision,), epsabs=2e-12)[0])

    zero, pair = integrate(False), integrate(True)
    # Independent mixture over the length of a complex Gaussian shift of unit variance and mean 1.
    radial_zero = quad(lambda r: 2*r*np.exp(-(r-1)**2)*i0e(2*r)
                       *neutral_probability(a*r*r, occupation), 0, 12,
                       points=[min(1., 1/scale)], epsabs=2e-12)[0]
    assert abs(zero-radial_zero) < 8e-10
    return zero, pair


def endpoint(s, weight, solar_mass, x=1.05, temperature=TEMP, radius=RADIUS):
    mass = 4*math.pi*DENSITY*radius**3/3
    omega = s*SHEAR_SPEED/radius
    time_left = 4*SOLAR_GM*solar_mass*x**1.5/(3*LIGHT**3)
    tide = 2/(9*time_left**2)
    z = omega*time_left
    transfer = response(z)
    coupling2 = weight*mass*radius**2
    equilibrium = coupling2*(6*tide**2)/(2*HBAR*omega**3)
    excess = equilibrium*abs(transfer)**2
    occupation = 1/math.expm1(HBAR*omega/(BOLTZMANN*temperature)) if temperature else 0.
    # A signed scalar read along a real material axis orthogonal to hypothesis 2.
    bright = .75*excess
    variance = bright*(2*occupation+1)
    nodes, weights = laguerre(80)
    derivative = np.dot(weights, -1j*nodes**2/(nodes+1j*z)**2)
    growth = (4 - 2*z*(derivative/transfer).real)/time_left
    gamma_g = 4*NEWTON*coupling2*omega**4/(5*LIGHT**5)
    diff_zero, diff_collision = matched_noise_probabilities(bright, occupation)
    return dict(solar_mass=solar_mass, radius_in_horizon_units=x, remaining_proper_s=time_left,
                tide_s_inv2=tide, omega_per_s=omega, strain_scale=tide*radius**2/SHEAR_SPEED**2,
                z=z, nonadiabatic_fraction=float(abs(transfer)**2),
                thermal_occupation=occupation, quasistatic_population=equilibrium,
                excess_population=float(excess), bare_population=float(equilibrium*abs(1-transfer)**2),
                bright_population=float(bright), bright_work_variance=variance,
                bright_zero=neutral_probability(bright, occupation),
                local_decision_error=neutral_probability(bright, occupation)/2,
                independent_pair_neutral=float(i0e(2*variance)),
                matched_diffusion_error=diff_zero/2, matched_diffusion_pair_neutral=diff_collision,
                signed_events_per_proper_s=growth*variance,
                gravitational_damping_per_s=gamma_g,
                excess_radiation_per_s=gamma_g*excess,
                # Upper bound on emitted excess from the infinite past using |A(omega*u)| <= |A(omega*t)|.
                excess_radiation_to_endpoint_bound=gamma_g*excess*time_left/3,
                bare_orientation_squared_fidelity_exponent=3*equilibrium*abs(1-transfer)**2/(2*occupation+1))


def clock_bound(b):
    if b < 1e-4:
        return 1-b/6+b*b/15-b**3/28
    return 2*math.atan(math.sqrt(b))/math.sqrt(b)-math.log1p(b)/b


def horizon_capture():
    """Same finite clock, arbitrary passive Gaussian cross-correlations, cooling grain."""
    from visible_body_flux import early_exposure
    tmax, tmin = 300., 285.
    bolometric = math.pi**2*BOLTZMANN**4/(60*HBAR**3*LIGHT**2)
    area = 4*math.pi*RADIUS**2
    mass = DENSITY*area*RADIUS/3
    heat_floor = 700.
    cooling = mass*heat_floor*(tmax-tmin)/(area*bolometric*tmax**4)
    # Fixed physical band [k*Tmax, 2*k*Tmax] with emissivity >= 0.1.
    band = quad(lambda k:k*k/math.expm1(k*tmax/tmin),1,2)[0]
    flux = .1*area*(BOLTZMANN*tmax/HBAR)**3*band/(4*math.pi**2*LIGHT**2)
    ratio = 1.4/3.2
    threshold = brentq(lambda n:clock_bound(.5*n*ratio**2)-.01,1e4,1e8)
    rows = []
    for solar in (3.,10.,100.,1e4,4.3e6):
        rs, exposure = early_exposure(solar)
        span = 2*rs/(3*LIGHT)*(5**1.5-3**1.5)
        # In a clipped window the comoving accepted sky fraction is >= 1/15000
        # at every point between x=5 and x=3, including arbitrarily large holes.
        exposure_lower = exposure if span<=cooling else cooling/15000
        count = flux*exposure_lower
        b = 2*count*ratio**2
        rows.append(dict(solar_mass=solar, full_fall_seconds=span, clipped=bool(span>cooling),
                         guaranteed_photons=count, radial_at_T0=clock_bound(b),
                         radial_for_any_longer=clock_bound(b/4),
                         minimum_efficiency_percent=100*threshold/count))
    assert rows[0]['radial_for_any_longer']<.01 and rows[-1]['radial_for_any_longer']<.01
    # Cross-coherence between arbitrary unequal energies and signs. Ground truth from
    # the complete Gaussian counting determinant and an independent intensity triangle bound.
    mat = np.array([[1,.2j,.7],[.3,-.1j,1.2],[-.7,.4,.1j],[.1,1.,-.33j]])
    cov = mat@mat.conj().T
    energy = np.array([1.4,-2.,2.7,-3.2])
    count = float(np.trace(cov).real)
    def char(t):
        det = np.linalg.det(np.eye(4)+cov@np.diag(1-np.exp(1j*t*energy)))
        return 1/det
    T0 = math.pi/3.2
    for t in np.linspace(0,T0,251):
        bound = 1/(1+count*2*(1.4*t/math.pi)**2)
        assert abs(char(t))<=bound+2e-13
    exact = quad(lambda y:2*(1-y)*char(y*T0).real,0,1)[0]
    upper = clock_bound(2*count*ratio**2)
    assert 0 <= exact <= upper and abs(upper-quad(lambda y:2*(1-y)/(1+2*count*ratio**2*y*y),0,1)[0])<2e-14
    for laplace_parameter in (.1, 1., 10., 1000.):
        exponent = quad(lambda e: -math.expm1(-laplace_parameter*e)*math.exp(-e)/e,
                        0, np.inf, epsabs=1e-12)[0]
        assert abs(exponent-math.log1p(laplace_parameter)) < 2e-12
    # A number-correlated nonclassical input with equal energies defeats a mean-only bound.
    return dict(initial_K=tmax, minimum_K=tmin, heat_capacity_floor_J_kg_K=heat_floor,
                cooling_guarantee_s=cooling, min_sky_fraction=1/15000,
                minimum_count_for_any_longer=threshold,
                large_hole_lower_count=flux*cooling/15000,
                crossover_solar_mass=3*cooling/rows[0]['full_fall_seconds'],
                accepted_band_ratio=ratio, cases=rows,
                infinite_soft_exponential_clock={str(t):clock_bound(t*t) for t in (1,10,1000)},
                unfactorized_check=dict(total_mean=count,exact_radial=exact,upper=upper),
                twin_equal_number=dict(each_port_mean=1000000,radial=1))


def run():
    spectrum = roots(.064, 135)
    comparison = roots(.028, 135)
    assert len(spectrum)==len(comparison) and np.max(np.abs(np.array(spectrum)-comparison)) < 2e-10
    weights = [mode_weight(s, 192) for s in spectrum]
    assert max(abs(w-mode_weight(s, 256)) for s,w in zip(spectrum,weights)) < 1e-12
    residual_force = 1/5-sum(weights)
    residual_static = NORM_COMPLIANCE-sum(w/s**2 for w,s in zip(weights,spectrum))
    assert 0 < residual_force < 1e-5 and 0 < residual_static < 1e-9
    zs = (0.5, 1., 3., 30., 300., 10000.)
    errors = [abs(response(z, 160)-response_fourier(z)) for z in zs]
    assert max(errors) < 5e-9
    s, w = spectrum[0], weights[0]
    cases = [endpoint(s,w,m) for m in (3,10,30,100,1e3,1e6,4.3e6)]
    local_limit = brentq(lambda m:endpoint(s,w,m)['local_decision_error']-.01, 2, 1000)
    pair_limit = brentq(lambda m:endpoint(s,w,m)['independent_pair_neutral']-.01, 2, 1000)
    cold_case = endpoint(s,w,10,temperature=0.)
    massive_limit = brentq(lambda radius:endpoint(s,w,4.3e6,radius=radius)['local_decision_error']-.01, .003, .2)
    massive_diff_limit = brentq(lambda radius:endpoint(s,w,4.3e6,radius=radius)['matched_diffusion_error']-.01, .003, .2)
    matched_mass_limit = brentq(lambda m:endpoint(s,w,m)['matched_diffusion_error']-.01, 2, 1000)
    # Resolve how much together all elastic overtones carry in the ordinary untagged local state.
    full_exponent = sum(endpoint(r,f,10)['bare_orientation_squared_fidelity_exponent']
                        for r,f in zip(spectrum,weights))
    # Model comparison for a grain at the adopted solar circle, under a spherical flat curve.
    orbit_radius = 8e3 * 3.085677581491367e16
    galactic_tide = (230e3/orbit_radius)**2
    # (4/3,-2/3,-2/3) in units v^2/r^2 gives squared STF norm 8/3.
    stored_fraction = (4/3)*NORM_COMPLIANCE*RADIUS**4*galactic_tide**2/(SHEAR_SPEED**2*LIGHT**2)
    # McKee, Parravano & Hollenbach (2015), eq. 46 and local dynamical estimate.
    baryon, baryon_error = .084, .012
    dark, dark_error = .013, .003
    general_limit = .1**2/70
    assert np.all(np.diff([case['bright_zero'] for case in cases]) >= 0)
    assert cases[-1]['local_decision_error'] > .49999 and cases[1]['local_decision_error'] < .002
    return dict(horizon=horizon_capture(), material=dict(density_kg_m3=DENSITY, bulk_Pa=BULK, shear_Pa=SHEAR,
                              shear_speed_m_s=SHEAR_SPEED, radius_m=RADIUS,
                              mass_kg=4*math.pi*DENSITY*RADIUS**3/3, temperature_K=TEMP),
                spectrum=dict(roots=spectrum, force_weights=weights,
                              first_share_of_static=(w/s**2)/NORM_COMPLIANCE,
                              missing_force_weight=residual_force, missing_compliance=residual_static,
                              dimensionless_static=NORM_COMPLIANCE, transform_check_max=max(errors)),
                cases=cases, local_one_percent_mass=local_limit, independent_pair_one_percent_mass=pair_limit,
                one_percent_radius_at_4_3e6_solar_m=massive_limit,
                matched_diffusion_one_percent_radius_at_4_3e6_solar_m=massive_diff_limit,
                matched_diffusion_one_percent_mass=matched_mass_limit,
                cold_ten_solar=cold_case, ten_solar_bare_orientation_exponent_resolved=full_exponent,
                galaxy=dict(radius_kpc=8, speed_km_s=230, flat_curve_quadrupole_stored_fraction=stored_fraction,
                            general_fraction_bound=general_limit,
                            baryon_midplane_msun_pc3=[baryon,baryon_error],
                            inferred_dark_msun_pc3=[dark,dark_error],
                            central_shortfall=dark/(general_limit*baryon),
                            conservative_shortfall=(dark-2*dark_error)/(general_limit*(baryon+2*baryon_error))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1]
                        / 'verification' / 'elastic-tidal-receipts-results.json')
    args = parser.parse_args()
    output = json.dumps(run(), indent=2, allow_nan=False)+'\n'
    args.output.write_bytes(output.encode('utf-8'))
    print('Elastic sphere and work statistics saved in', args.output)
