"""Causal spherical accretion and angular information in the outgoing radiation.

Run from any working directory with Python 3, NumPy and SciPy. SI units in
the infall calculation. Times and areas in the radiation tests are normalized to their initial scales.
"""
import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import eval_legendre, roots_legendre, log_ndtr

ROOT = Path(__file__).resolve().parents[1]
C, G, HBAR = 299792458.0, 6.67430e-11, 1.054571817e-34
SOLAR_MASS = 1.98847e30


def transit(solar_mass, added_mass, width, tube_ratio):
    outer_mass = solar_mass * SOLAR_MASS
    mass_fraction = added_mass / outer_mass
    r_plus = 2 * G * outer_mass / C**2
    radius = tube_ratio * r_plus
    distance = (tube_ratio - 1) * r_plus
    b = math.sqrt((1 - mass_fraction) / tube_ratio)
    lapse_upper = math.sqrt((tube_ratio - 1 + mass_fraction) / tube_ratio)
    early = distance / C * b / (1 + b)
    late = distance / C * (1 / b - 0.5)
    duration = (2 * radius * math.sqrt(tube_ratio) / (3*C)
                * math.expm1(1.5 * math.log1p(width / radius)))
    quiet_time = late * lapse_upper
    probe_radius = width / 2
    tidal_delta = G * added_mass / radius**3
    distinguishability_per_kg = 0.75 * tidal_delta * probe_radius**2 * quiet_time / HBAR
    assert duration < early
    angular_reach = distance/(b*r_plus)
    mean_column = added_mass/(math.pi*probe_radius**2)
    # Separate flat-rest pencil through a localized body of projected area pi*l^2.
    focusing_step = 8*math.pi*G*mean_column/C**2
    delay_factor = math.asinh(10)-math.asinh(5)
    local_delay = 4*G*added_mass*delay_factor/C**3
    pi_energy = math.pi*HBAR/local_delay
    return dict(optical_delay_s_for_ten_radii=local_delay,
                optical_pi_energy_J=pi_energy, optical_pi_over_body_energy=pi_energy/(added_mass*C**2),
                angular_radius_bound_before_front_rad=angular_reach,
                accessible_fraction_bound=math.sin(min(math.pi,angular_reach)/2)**2,
                flat_rest_mean_ricci_step_per_m=focusing_step,
                solar_mass=solar_mass, added_mass_kg=added_mass, width_m=width,
                tube_over_r_plus=tube_ratio, crossing_s=duration,
                sufficient_processing_budget_pg_s=early-duration,
                latest_launch_pg_s=late, plateau_proper_time_upper_s=quiet_time,
                same_mass_probe_trace_distance_upper=min(1.0, added_mass * distinguishability_per_kg),
                necessary_probe_mass_kg_for_trace_distance_099=0.99/distinguishability_per_kg,
                same_shell_time_from_r_plus_to_zero_s=2*r_plus/(3*C))


def check_null_arrival():
    # Dimensionless R/r_plus, c*tau/r_plus. Large relative self-gravity
    # makes the independent null integrator sensitive to the LTB mass profile.
    mu, radius, width = 0.01, 1.12, 0.012

    def mass(a):
        return 1-mu+mu*a*a*(3-2*a)

    def dust(a, time):
        return ((radius+width*a)**1.5 - 1.5*math.sqrt(mass(a))*time)**(2/3)

    def interior_mass(r, time):
        if r <= dust(0, time):
            return 1-mu
        if r >= dust(1, time):
            return 1.0
        a = brentq(lambda a: dust(a, time)-r, 0, 1)
        return mass(a)

    def arrival(delay, tolerance):
        def inward(time, state):
            return [-1-math.sqrt(interior_mass(state[0], time)/state[0])]

        def reached(time, state):
            return state[0]-1
        reached.terminal = True
        reached.direction = -1
        path = solve_ivp(inward, (delay, delay+0.2), [radius], events=reached,
                         max_step=0.0008, rtol=tolerance, atol=tolerance*0.02)
        return float(path.t_events[0][0])

    crossing = (2/3)*((radius+width)**1.5-radius**1.5)
    leading = (2/3)*(radius**1.5-1)/math.sqrt(1-mu)
    b = math.sqrt((1-mu)/radius)
    sufficient = (radius-1)*b/(1+b)
    latest = (radius-1)*(1/b-0.5)
    critical_delay = brentq(lambda t: arrival(t, 1e-10)-leading, crossing, leading)
    assert crossing < sufficient < critical_delay < latest
    def inverse_ray(r, state):
        return [-1/(1+math.sqrt(interior_mass(r, state[0])/r))]
    inverse = solve_ivp(inverse_ray, (radius, 1.), [crossing], method="DOP853",
                        max_step=0.00073, rtol=2e-12, atol=1e-14)
    convergence = abs(arrival(crossing, 1e-9)-float(inverse.y[0,-1]))
    assert convergence < 1e-7
    # Check the derivative of the shell-focusing time from this mass profile.
    points = np.linspace(0, 1, 401)
    dt_sign = 3*width*mass(points) - (radius+width*points)*6*mu*points*(1-points)
    assert min(dt_sign) > 0
    return dict(delta_mass_fraction=mu, tube=radius, radial_width=width,
                shell_crossing=crossing, leading_arrival=leading,
                inward_arrival_after_tail=arrival(crossing, 2e-12),
                latest_safe_bound=sufficient, latest_possible_bound=latest,
                numerical_critical_launch=critical_delay, integration_difference=convergence)


def angular_bins(count):
    edges = np.linspace(-1, 1, count+1)
    # Integrate |Y_10|^2 and |Y_1,+1|^2 over azimuth and each polar bin.
    central = np.diff(edges**3)/2
    side = 0.75*np.diff(edges)-0.5*central
    assert min(central) > 0 and min(side) > 0
    assert abs(sum(central)-1) < 1e-12 and abs(sum(side)-1) < 1e-12
    fidelity = float(sum((np.sqrt(central)+2*np.sqrt(side))**2)/9)
    return dict(bins=count, optimum_flagged_qutrit_fidelity=fidelity)


def two_quantum_contacts():
    # Direct integration of translated two-component wavefunctions against Q,
    # compared with the local Pauli-matrix expression after conjugation by D1.
    nodes, weights = roots_legendre(112)
    x, z = np.meshgrid(11*nodes, 11*nodes, indexing="ij")
    area = 121*np.outer(weights,weights)
    def packet(x1, x2, phase):
        first = np.exp(-((x1-0.33)**2+(x2+0.2)**2)/2)*(1+0.15j*x1)
        second = phase*np.exp(-((x1+0.22)**2+(x2-0.4)**2)/2)*(0.3+x2+0.17j)
        return first, second
    g1, g2 = 0.73, 0.41
    errors = []
    for phase in (1.,1j,-0.4+0.3j):
        first, second = packet(x,z,phase)
        fminus, sminus = packet(x,z-g2,phase)
        fplus, splus = packet(x,z+g2,phase)
        plus, minus = (fminus+sminus)/2, (fplus-splus)/2
        out_density = abs(plus+minus)**2+abs(plus-minus)**2
        back_density = abs(packet(x+g1,z,phase)[0])**2+abs(packet(x-g1,z,phase)[1])**2
        direct = np.sum(area*(x*x+z*z)*(out_density-back_density))
        density = abs(first)**2+abs(second)**2
        contrast = abs(first)**2-abs(second)**2
        interference = 2*np.real(first.conj()*second)
        expected = np.sum(area*((g2*g2-g1*g1)*density+2*g1*x*contrast+2*g2*z*interference))
        errors.append(float(abs(direct-expected)/np.sum(area*density)))
    assert max(errors) < 1e-12
    return dict(first_shift=g1,second_shift=g2,wavefunction_matrix_element_errors=errors)


def neutral_dipole():
    # Ground-vibrational-state effective dipole magnitude of isolated water.
    dipole = 1.8546*3.33564e-30
    epsilon0 = 8.8541878128e-12
    inner, outer = 1e-9, 2e-9
    axis = np.array([0., 0., 1.])
    u, w = roots_legendre(12)
    angles = np.arange(24)*2*math.pi/24
    checks = []
    for cosine in (0., 0.37, 1.):
        direction = np.array([math.sqrt(1-cosine**2), 0., cosine])
        average = 0.
        for cos_theta, weight in zip(u, w):
            transverse = math.sqrt(1-cos_theta**2)
            for phi in angles:
                normal = np.array([transverse*math.cos(phi),transverse*math.sin(phi),cos_theta])
                field = 3*np.dot(direction,normal)*normal-direction
                average += weight*(np.dot(field,field)-np.dot(axis,field)**2)/(2*len(angles))
        predicted = (7-cosine**2)/5
        assert abs(average-predicted) < 1e-13
        energy = dipole**2*(7-cosine**2)*(inner**-3-outer**-3)/(60*math.pi*epsilon0)
        checks.append(dict(axis_cosine=cosine, angular_integral=average, integrated_null_stress_J=energy))
    return dict(inner_radius_m=inner, outer_radius_m=outer, diameter_light_time_s=2*outer/C,
                orientations=checks)


def quantum_pencil():
    # Fourier convention: dPi=d^3p/((2*pi)^3*2p), Wtilde(P)=exp(-|P|_E^2/2).
    # Evaluate the original two-particle vacuum integral before reducing to
    # total four-momentum. Azimuthal integration gives I_0.
    coeff = (math.pi/16-1/15)/(160*math.pi**4)
    def two_particle(order):
        nodes, weights = roots_legendre(order)
        p = 3*(nodes+1)
        wp = 3*weights*p**3
        polar = np.outer(weights*(1-nodes)**2, weights*(1-nodes)**2)
        cosines = np.outer(nodes, nodes)
        transverse = np.sqrt(np.outer(1-nodes**2, 1-nodes**2))
        total = 0.
        for i, first in enumerate(p):
            for j, second in enumerate(p):
                twice = 2*first*second
                kernel = np.exp(-2*(first**2+second**2)-twice*(1+cosines))*np.i0(twice*transverse)
                total += wp[i]*wp[j]*np.sum(polar*kernel)
        return total/(2*(2*math.pi)**4)
    values = [two_particle(n) for n in (16, 28)]
    assert abs(values[-1]-coeff) < 1e-14
    def finite_read(y):
        # Q_rel=y^2+2*y*X for a unit vacuum quadrature. A finite threshold
        # discards very weak signals even though a nonzero y has no zero atom.
        mean, spread, threshold = y*y, 2*y, 0.1
        log_probability = float(np.logaddexp(log_ndtr((-threshold-mean)/spread),
                                             log_ndtr((mean-threshold)/spread)))
        row = dict(source=y, log10_accepted=log_probability/math.log(10))
        if log_probability > -700:
            row["accepted"] = math.exp(log_probability)
        return row
    return dict(vacuum_variance_coefficient=coeff, direct_quadratures=values,
                threshold=0.1, source_and_detection=[finite_read(y) for y in (1.,0.1,0.01,0.001)])


def evaporation_output():
    # x is fractional horizon area. Use shifted Legendre modes to test
    # complex superpositions as well as their individual norms.
    def gram_entry(i, j, gamma):
        def density(y):
            x = y**gamma
            return (gamma*y**(gamma-1) * math.sqrt((2*i+1)*(2*j+1))
                    * eval_legendre(i, 2*x-1) * eval_legendre(j, 2*x-1))
        return quad(density, 0., 1., epsabs=5e-12, limit=180)[0]
    errors = []
    for gamma in (2/3, 3.):
        gram = np.array([[gram_entry(i, j, gamma) for j in range(6)] for i in range(6)])
        errors.append(float(np.max(np.abs(gram-np.eye(6)))))
    assert max(errors) < 3e-10
    # phi=sqrt(3)*(1-x) is normalized, starts smoothly and is nonzero at x=0.
    def exterior_lower(gamma, ymin):
        return quad(lambda y: 3*gamma*y**(gamma-2)*(1-y**gamma)**2,
                    ymin, 1., epsrel=2e-11)[0]
    tails = [dict(remaining_time_cut=cut,
                  hawking_cross_term_half=exterior_lower(2/3,cut),
                  cubic_cross_term_half=exterior_lower(3.,cut))
             for cut in (0.1, 0.01, 0.001, 0.0001)]
    # With cubic shrinkage b(u)=3*y*(1-y^3), y=1-u, extended by zero.
    h1_energy_sq = quad(lambda y: 9*(1-4*y**3)**2, 0., 1.)[0]
    assert abs(h1_energy_sq-81/7) < 1e-12
    assert abs(exterior_lower(3.,0)-81/40) < 1e-12
    return dict(max_gram_error_for_each_area_law=errors, endpoint_integrals=tails,
                cubic_mean_energy_bound_hbar_over_duration=math.sqrt(h1_energy_sq))


def final_record():
    rows = []
    for ratio in (1., 1.21, 2., 4., 10.):
        overlap = quad(lambda t: math.sqrt(ratio)*math.exp(-(1+ratio)*t/2),
                       0., math.inf)[0]
        assert abs(overlap-2*math.sqrt(ratio)/(1+ratio)) < 1e-12
        rows.append(dict(width_ratio=ratio, lifetime_record_visibility=overlap,
                         optimum_logical_qubit_fidelity=(1+overlap)/2))
    return rows


def run():
    examples = [transit(solar, mass, length, ratio)
                for solar in (3., 30., 4e6, 1e9)
                for mass, length in ((2200*math.pi*(1e-4)**3/6, 1e-4), (70., 1.7))
                for ratio in (1.05, 1.2)]
    bins = [angular_bins(n) for n in (1, 2, 4, 8, 64, 1024)]
    limit = (5+2*math.sqrt(2))/9
    overlap = quad(lambda u: 2*math.sqrt(9/8)*u*math.sqrt(1-u*u), 0., 1.)[0]
    assert abs(overlap-1/math.sqrt(2)) < 1e-12
    assert abs(bins[1]["optimum_flagged_qutrit_fidelity"]-1) < 1e-12
    assert all(row["optimum_flagged_qutrit_fidelity"]+1e-13 >= limit for row in bins)
    assert abs(bins[-1]["optimum_flagged_qutrit_fidelity"]-limit) < 2e-5
    emission = evaporation_output()
    return dict(spherical_shells=examples, nonlinear_null_check=check_null_arrival(),
                quantum_pencil=quantum_pencil(), neutral_dipole=neutral_dipole(),
                noncommuting_source=two_quantum_contacts(),
                angular_records=bins, continuous_polar_qutrit_fidelity=limit,
                areal_release=emission, final_waiting_time_records=final_record())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT/"verification"/"causal-mass-evaporation-results.json")
    output = parser.parse_args().output
    output.write_text(json.dumps(run(), indent=2, allow_nan=False)+"\n", encoding="utf-8")
    print(output.name)
