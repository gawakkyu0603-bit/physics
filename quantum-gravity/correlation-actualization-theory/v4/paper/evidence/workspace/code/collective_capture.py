"""Gravitational exchange in warm matter and a many-layer radial threshold.

Run from the project with python -B code/collective_capture.py. All numerical
figures refer to the effective model, not to a measured population of clumps.
"""
from itertools import product
from math import expm1, pi, sqrt
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.constants import G, Boltzmann, c, hbar
from scipy.integrate import quad
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parents[1]


def thermal_width(activity):
    """Half the mean absolute difference of two independently formed transfers."""
    return 2 * activity * (1 + 3 * activity) / (1 + 4 * activity)**1.5


def occupation_distribution():
    # Independent construction of transition probabilities in fixed-number sectors.
    probability = 0.23
    angle = np.arcsin(sqrt(probability))
    checks = []
    for n_source, n_receiver in [(0.38, 0.38), (0.65, 0.14), (0.41, 0.0)]:
        a = probability * n_source * (1 + n_receiver)
        b = probability * n_receiver * (1 + n_source)
        cutoff = 27
        counts = np.zeros(2 * cutoff + 1)
        for number in range(cutoff + 1):
            label = np.arange(1, number + 1)
            exchange = np.diag(np.sqrt(label * (number - label + 1)), 1) if number else np.zeros((1, 1))
            unitary = expm(-1j * angle * (exchange + exchange.T))
            for initial in range(number + 1):
                source_initial = number - initial
                prior = ((n_source / (1 + n_source))**source_initial / (1 + n_source)
                         * (n_receiver / (1 + n_receiver))**initial / (1 + n_receiver))
                targets = cutoff + np.arange(number + 1) - initial
                counts[targets] += prior * abs(unitary[:, initial])**2
        marks = np.arange(-cutoff, cutoff + 1)
        chi = np.linspace(0, 2 * pi, 51)
        analytic = 1 / (1 + a * (1 - np.exp(1j * chi)) + b * (1 - np.exp(-1j * chi)))
        residual = max(abs(np.exp(1j * np.outer(chi, marks)) @ counts - analytic))
        assert residual < 2e-11
        width = sum(p * sum(counts * abs(marks - z)) for p, z in zip(counts, marks)) / 2
        if n_source == n_receiver:
            assert abs(width - thermal_width(a)) < 1e-10
        checks.append(dict(source=n_source, receiver=n_receiver, fock_error=float(residual),
                           probability_zero=float(counts[cutoff]), relative_work_quanta=float(width)))
    return checks


def tensor_spectrum():
    # Fourier transform of d_i d_j d_k d_l(1/r) on a straight line r=(1,t,0).
    # Isotropic orientations trace the squared STF tensor. Enumerating all
    # Cartesian components provides a check independent of the time-domain norm.
    def component(t, axes):
        rad = np.hypot(1, t)
        n = np.array([1, t, 0]) / rad
        i, j, k, l = axes
        delta = int
        two = (delta(i == j)*n[k]*n[l] + delta(i == k)*n[j]*n[l] +
               delta(i == l)*n[j]*n[k] + delta(j == k)*n[i]*n[l] +
               delta(j == l)*n[i]*n[k] + delta(k == l)*n[i]*n[j])
        zero = delta(i == j)*delta(k == l) + delta(i == k)*delta(j == l) + delta(i == l)*delta(j == k)
        return (105*n[i]*n[j]*n[k]*n[l] - 15*two + 3*zero) / rad**5

    axes_all = list(product(range(3), repeat=4))
    for t in (0.0, .7, 2.3):
        trace = sum(component(t, axes)**2 for axes in axes_all)
        assert abs(trace * (1 + t*t)**5 / 2520 - 1) < 3e-14
    orientation = (4/225) * sum(quad(lambda t: component(t, axes), -np.inf, np.inf)[0]**2
                                   for axes in axes_all) / 144
    assert abs(orientation - 32/225) < 2e-12
    # FFT directly integrates the encounter, including nonzero detunings.
    nt = 16384
    step = 0.0125
    t_grid = (np.arange(nt) - nt/2) * step
    angular_frequency = np.fft.rfftfreq(nt, step) * 2*pi
    power = np.zeros_like(angular_frequency)
    for axes in sorted(set(tuple(sorted(a)) for a in axes_all)):
        count = sum(tuple(sorted(a)) == axes for a in axes_all)
        rad = np.hypot(1, t_grid)
        vec = np.array([1/rad, t_grid/rad, np.zeros(nt)])
        i, j, k, l = axes
        indices = list(axes)
        pairs = 0.
        for a in range(4):
            for b in range(a):
                if indices[a] == indices[b]:
                    rest = [indices[h] for h in range(4) if h not in (a, b)]
                    pairs += vec[rest[0]] * vec[rest[1]]
        zero = int(i == j and k == l) + int(i == k and j == l) + int(i == l and j == k)
        curve = (105*vec[i]*vec[j]*vec[k]*vec[l] - 15*pairs + 3*zero) / rad**5
        power += count * (4/225) * abs(np.fft.rfft(curve) * step)**2
    trap = getattr(np, "trapezoid", None) or np.trapz
    area = 2 * trap(power, angular_frequency)
    exact = 49 * pi*pi / 2
    assert abs(area/exact - 1) < 2e-12
    smooth = 2 * trap(power * np.exp(-0.5*(angular_frequency/24)**2), angular_frequency) / exact
    assert 1 - 45/(2*24**2) < smooth < 1
    return dict(isotropic_on_resonance=orientation, integrated_response=float(area),
                analytic_integral=exact, gaussian_ratio_at_24=float(smooth))


def cloud():
    length, mass = 10., 2.5e6
    speed, omega, temperature = 10., 300., 30.
    low, high = 76., 84.
    density, edge, exposure, frequency_spread = 1.e-9, 3.e6, 1000., 3.
    number = 1/expm1(hbar*omega/(Boltzmann*temperature))
    coefficient = G*mass*length**2/(8*omega)
    phase_at = lambda b: 12*coefficient/(speed*b**4)
    probability_density_zero = 1/(sqrt(2*pi)*frequency_spread)
    # The rate weights b db and integrates the actual encounter time and orientations.
    def mean_activity_density(b):
        integrated_transfer = 49*pi*pi*coefficient**2/(2*speed*b**9)
        pairs_per_radius = density**2 * edge**3 * exposure * 2*pi*speed*b
        return pairs_per_radius * probability_density_zero * integrated_transfer * number*(1+number)
    activity_sum = quad(mean_activity_density, low, high)[0]
    shape_lower = 1 - 45*speed**2/(2*(frequency_spread*low)**2)
    # All angular contractions are bounded by the tensor norm. Time integral of r^-5 is 4/(3vb^4).
    amplitude_ceiling = sqrt(2520) * 4*coefficient/(3*speed*low**4)
    activity_ceiling = number*(1+number)*amplitude_ceiling**2
    linear_lower = (1+3*activity_ceiling)/(1+4*activity_ceiling)**1.5
    lower_units, upper_units = 2*activity_sum*shape_lower*linear_lower, 2*activity_sum
    total_encounters = pi*(high**2-low**2)*density**2*speed*edge**3*exposure
    # A relative spread of <= 25% covers omitted contacts only when physically bounded.
    per_encounter_max = thermal_width(activity_ceiling)
    return dict(length_m=length, mass_kg=mass, speed_m_s=speed, omega_s=omega, temperature_K=temperature,
                density_each_m3=density, cloud_edge_m=edge, counted_midpoints_s=exposure,
                impact_band_m=[low, high], detuning_sigma_s=frequency_spread,
                quadrupole_expansion=(length/low)**2, occupation=number,
                central_mixing_angle=phase_at(80.), completed_encounters=total_encounters,
                expected_activity=activity_sum, band_correction_floor=shape_lower,
                largest_event_activity=activity_ceiling, weak_write_floor=linear_lower,
                work_units=[lower_units, upper_units], work_joule=[hbar*omega*lower_units,hbar*omega*upper_units],
                maximum_work_per_event=per_encounter_max, poisson_variance_ceiling=per_encounter_max*upper_units,
                mean_nonzero_bounds=[2*activity_sum*shape_lower/(1+4*activity_ceiling)**1.5, 2*activity_sum],
                gravity_to_orbit=G*2*mass/(low*speed**2), crossing_light_s=edge/c,
                parcel_mass_kg=2*mass*density*edge**3, time_5b_each_side_s=10*high/speed,
                flyby_quality_needed=omega*(10*high/speed), single_mode_thermal_energy_J=hbar*omega*number)


def frontier(cl):
    # Open, conditional range: about 98 percent of relative work is fixed in A,
    # at least 90 percent is unresolved in B. The test allows leakage and finite time.
    w_min, w_max = cl["work_units"]
    variance = cl["poisson_variance_ceiling"]
    # One-sided variance inequality applied to the random completed-work sum (in quanta).
    k = 10
    capacity_low = w_min - k*sqrt(variance)
    capacity_high = w_max + k*sqrt(variance)
    a = .02 * capacity_high
    b = .9 * capacity_low
    e1, e2 = 18., 36.
    pa = 4 * sqrt(1-a/e1) / (1+sqrt(1-a/e1))**2
    omega = cl["omega_s"]
    delay = 1 / (omega * sqrt(min(e1*(b-e1),e2*(b-e2))))
    packet_time = pi / (omega * (e2-e1))
    assert a < e1 < e2 < b
    return dict(work_window=[capacity_low,capacity_high], failure_each_side=1/(1+k*k),
                thin_ceiling=a, thick_floor=b, energy_band=[e1,e2], falling_flux_floor=pa,
                maximum_group_delay_s=delay, packet_time_rms_s=packet_time,
                chance_outside_50ms=(delay**2+packet_time**2)/.05**2,
                allowed_unlocked_energy_joule=(b-e2)*hbar*omega,
                all_heat_over_threshold=(cl["completed_encounters"]*cl["single_mode_thermal_energy_J"]
                                         /(hbar*omega*b)))



def hydrogen_rotor():
    from scipy.special import i0e, i1e
    from scipy.constants import atomic_mass
    wavelength = 28.22e-6
    omega = 2*pi*c/wavelength
    molecular_mass = 2.01588*atomic_mass
    radius = 2*G*1.98847e36 / c**2  # 10^6 solar masses
    rate = (12/25) * (G*hbar/c**5) * omega**3
    temperature = 300.
    j = np.arange(35)
    boltzmann = np.exp(-hbar*omega*j*(j+1)/(6*Boltzmann*temperature))
    degeneracy = (2*j+1)*np.where(j%2 == 0, 1, 3)
    p2 = float((degeneracy*boltzmann)[2] / sum(degeneracy*boltzmann))
    # Independently integrate the angular J=2,m=0 matrix element of the STF mass quadrupole.
    qzz = sqrt(5)/4 * quad(lambda u: (3*u*u-1)*(u*u-1/3), -1, 1)[0]
    inertia = 3*hbar/omega
    angular_rate = 2*G*omega**5/(5*hbar*c**5)*1.5*(qzz*inertia)**2
    assert abs(angular_rate/rate - 1) < 2e-15

    def axial_geometry(spin, energy, cone):
        rplus = 1+sqrt(1-spin*spin)  # lengths in G M/c^2
        b2 = cone**2*(rplus*rplus+spin**2)/energy**2
        def integrand(r):
            area = r*r+spin**2
            f = (r*r-2*r+spin**2)/area
            beta = sqrt(1-f/energy**2)
            s2 = b2*f/area
            cosine = sqrt(1-s2)
            # Positive form of (1-cosine)(1+beta)/[2(1-beta*cosine)].
            captured = s2*(1+beta)/(2*(1+cosine)*(1-beta*cosine))
            return captured/sqrt(energy**2-f)
        return quad(integrand,3*rplus,5*rplus)[0]/2  # in Schwarzschild light-crossing times

    cloud_mass = 5.9722e24
    routes = []
    for cone in (0.1,0.8):
        factor = axial_geometry(0,1,cone)
        useful_time = factor*radius/c
        count = cloud_mass/molecular_mass*p2*rate*useful_time
        rows = []
        for bins in (1, 64, 1000000):
            per_bin = count/bins
            cum = count*(i0e(2*per_bin)+i1e(2*per_bin))
            rows.append(dict(bins=bins,relative_work_in_line_quanta=cum))
        routes.append(dict(impact_fraction=cone,early_seconds=useful_time,expected_hits=count,
                           one_hit_mass_kg=cloud_mass/count,works=rows))
    def advance_savings(r0, b):
        def difference(r):
            f = 1-1/r
            particle, photon = sqrt(1-f), sqrt(1-f*b*b/r**2)
            return (1-b*b/r**2)/(particle*photon*(particle+photon))
        return quad(difference,1,r0)[0]
    delay = advance_savings(3,.1)
    angle = quad(lambda r:.1/(r*r*sqrt(1-(1-1/r)*.1**2/r**2)),1,5)[0]
    # A timelike exterior representation at 1.05 R can relay sooner than the matter reaches it.
    rs = 1.05
    lateral = rs/sqrt(1-1/rs)*angle
    advance_surface = advance_savings(3,.1) - advance_savings(rs,.1)
    assert lateral < advance_surface
    # Direct Poisson convolution, independent of the Bessel expression.
    from scipy.stats import poisson
    from scipy.optimize import brentq
    for mean in (.02, 1., 7., 54.):
        indices = np.arange(int(mean+14*sqrt(mean+1)+25))
        prob = poisson.pmf(indices,mean)
        direct = np.sum(prob[:,None]*prob[None,:]*abs(indices[:,None]-indices[None,:]))/2
        assert abs(direct - mean*(i0e(2*mean)+i1e(2*mean)))<2e-12
    early_count = routes[0]["expected_hits"]
    def work64(fraction):
        y = 2*early_count*fraction/64
        return early_count*fraction*(i0e(y)+i1e(y))
    a_uncertain = brentq(lambda u:work64(u)-10,0,1)
    uniform_exposure = .1**2/(260*1.15**3)
    all_spin_lower = cloud_mass/molecular_mass*p2*rate*(radius/c)*uniform_exposure
    from scipy.special import ive
    absolute_fraction = float(i0e(2*early_count))
    split_ports = float(i0e(early_count))
    moduli = {str(q):float(np.mean(np.exp(-2*early_count*(1-np.cos(2*pi*np.arange(q)/q)))))
              for q in (2,16,64,128,256)}
    screened = {str(s):float(sum(ive(abs(k),2*early_count) for k in range(-s,s+1)))
                for s in (0,1,10,50,100)}
    for q in (2,16,64,128,256):
        # Independent convolution on the cyclic group by aliasing Poisson weights.
        k = np.arange(int(early_count+12*sqrt(early_count)))
        modprob = np.bincount(k%q,weights=poisson.pmf(k,early_count),minlength=q)
        assert abs(modprob@modprob-moduli[str(q)]) < 2e-12
    u99 = brentq(lambda f:64*np.log(i0e(2*early_count*f/64))-np.log(.99),0,.001)
    selection = dict(single_flux_radial=absolute_fraction,disjoint_half_apertures_radial=split_ports,
                     radial_log10_64=64*float(np.log10(i0e(2*early_count/64))),
                     cyclic_modulus_radial=moduli,screened_radial=screened,unshared_fraction_99=u99)
    em_rate = 2.94e-11
    kerr_cases = [[spin,e,axial_geometry(spin,e,.1)] for spin in (0.,.5,.9,.998)
                  for e in (.95,1.,1.15)]
    return dict(neutral_flux_constraint=selection,line_m=wavelength,omega_s=omega,graviton_decay_s=rate,independent_angular_rate_s=angular_rate,
                black_hole_radius_m=radius,temperature_K=temperature,population_J2=p2,
                gas_mass_kg=cloud_mass,mass_per_molecule_kg=molecular_mass,
                prompt_cones=routes,kerr_exposure_in_R_over_c=kerr_cases,
                guaranteed_advance_in_R_over_c=delay,largest_angular_offset_rad=angle,
                surface_1p05_advance_R_over_c=advance_surface,surface_light_relay_R_over_c=lateral,
                gravitational_fraction_among_radiative_decays=rate/(rate+em_rate),
                static_energy_floor_J=hbar*omega, greybody_geometric_optics=omega*radius/c,
                all_spin_axial_lower_hits=all_spin_lower, local_unknown_fraction_for_10_quanta=a_uncertain,
                max_prompt_work_over_rest_energy=early_count*(1+1/sqrt(3))*hbar*omega/(cloud_mass*c*c),
                one_particle_source_70kg_hits=70*early_count/cloud_mass)


def main():
    cf = cloud()
    result = dict(occupation_checks=occupation_distribution(), isotropic_spectrum=tensor_spectrum(),
                  cloud=cf, routes=frontier(cf), hydrogen=hydrogen_rotor())
    (ROOT/"verification"/"collective-capture-results.json").write_text(
        json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    scale = np.geomspace(.01, 5, 300)
    low, high = cf["work_units"]
    fig, (ax, gas) = plt.subplots(1, 2, figsize=(8.0,3.1),layout="constrained")
    ax.fill_between(scale,.9*low*scale,high*scale,color="#176971",alpha=.38,label="Distant history (90–100% unresolved)")
    ax.fill_between(scale,.002*low*scale,.02*high*scale,color="#cd6b29",alpha=.42,label="Falling history (0.2–2% unresolved)")
    ax.axhspan(18,36,color="#595264",alpha=.18,label="Incident radial surplus")
    ax.axvline(1,color=".35",ls=":",lw=1)
    ax.set(xscale="log",yscale="log",xlabel="Causally participating volume / reference volume",
           ylabel=r"Relative work in units of $\hbar\omega$",ylim=(.02,2200))
    ax.legend(frameon=False,fontsize=8)
    count = result["hydrogen"]["prompt_cones"][0]["expected_hits"]
    counts = count*scale
    from scipy.special import i0e, i1e
    for bins,col in ((1,"#73405a"),(64,"#b47b23"),(1000000,"#176971")):
        y = 2*counts/bins
        gas.plot(scale,counts*(i0e(y)+i1e(y)),color=col,label=f"{bins:,} arrival bins")
    gas.set(xscale="log",yscale="log",xlabel="Warm molecular mass / Earth mass",
            ylabel="Relative work in molecular-line quanta")
    gas.legend(frameon=False,fontsize=7)
    (ROOT/"manuscripts").mkdir(exist_ok=True)
    fig.savefig(ROOT/"manuscripts"/"collective_capture.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    print(json.dumps(result["routes"],ensure_ascii=True))


if __name__ == "__main__":
    main()
