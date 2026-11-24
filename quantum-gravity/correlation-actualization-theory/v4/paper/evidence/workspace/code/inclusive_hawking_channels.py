"""Resolved exterior channels of a neutral Schwarzschild surface in four dimensions.

x = omega/T_H and the horizon length is r_s. The Page comparison uses the
particle content of his massless example. A separate massive scalar tests the
timelike flux; it is not included in that example's luminosity.
"""
from math import pi, sqrt

import numpy as np
from scipy.constants import G, c, electron_volt, hbar
from scipy.integrate import simpson
from scipy.interpolate import PchipInterpolator
from scipy.special import xlogy

from directional_absorption import transmission
from fusion_surface_memory import greybody


def massless_species():
    step = .0625
    x = np.arange(step, 36 + step/2, step)
    grid = np.r_[0., x]
    content = (("neutrino", .5, 4, range(1, 5)),
               ("photon", 1, 2, range(1, 6)),
               ("graviton", 2, 2, range(2, 7)))
    species = {}
    interpolants = {}
    for name, spin, states, partials in content:
        number = energy = entropy = 0.
        tagged = 0.
        partial_power = []
        curves = []
        for ell in partials:
            if spin == .5:
                coarse, fine = (transmission(x, ell, scale) for scale in (2, 4))
                degeneracy = 2*ell
            else:
                coarse, fine = (greybody(x/(4*pi), ell, scale, spin) for scale in (2, 4))
                degeneracy = 2*ell+1
            trans = fine + (fine-coarse)/15
            assert trans.min() > 0 and trans.max() < 1.00005
            trans = np.minimum(trans, 1)
            curves.append((PchipInterpolator(grid, np.r_[0., trans]), degeneracy*states))
            u = np.exp(-x)
            mean = u/(1+u) if spin == .5 else u/(1-u)
            density = degeneracy*states*trans*mean
            integrate = lambda values: float(simpson(np.r_[0., values], x=grid))
            number += integrate(density)
            outgoing = trans*mean
            if spin == .5:
                mode_entropy = -xlogy(outgoing, outgoing)-xlogy(1-outgoing, 1-outgoing)
            else:
                mode_entropy = (1+outgoing)*np.log1p(outgoing)-xlogy(outgoing, outgoing)
            entropy += degeneracy*states*integrate(mode_entropy)
            power = integrate(x*density)
            energy += power
            partial_power.append(power/(128*pi**3))
            if ell == partials.start:
                eligible = u/(1+u)**2 if spin == .5 else u*(1-u)**2
                tagged = integrate(trans*eligible)/integrate(x*trans*mean)
        species[name] = dict(power_M2=energy/(128*pi**3), number_times_M=number/(16*pi**2),
                             partial_powers=partial_power, first_tagged_per_entropy=tagged,
                             maximum_mode_entropy_over_own_area_loss=entropy/energy)
        interpolants[name] = curves
    total_power = sum(row["power_M2"] for row in species.values())
    total_number = sum(row["number_times_M"] for row in species.values())
    for row in species.values():
        row["power_fraction"] = row["power_M2"]/total_power
        row["number_fraction"] = row["number_times_M"]/total_number
        row["maximum_entropy_per_total_area_nat"] = (row["power_fraction"]
                                    *row["maximum_mode_entropy_over_own_area_loss"])
    for name, rounded_percentage in zip(species, (81, 17, 2)):
        assert round(100*species[name]["power_fraction"]) == rounded_percentage
    return species, interpolants


def inclusive_rates(curves, amplitudes, n=32768, dimension=16):
    """Sum Gram matrices over orthogonal outgoing species and partial waves.

    A Gaussian retarded-time window of rms width u gives overlap
    exp(-u**2*(omega_1-omega_2)**2/2). Recoil wavepackets are assumed to
    overlap in this example. Each parent uses its own physical rest clock.
    """
    m = np.arange(1, n+dimension)
    parent = n+np.arange(dimension)
    signs = np.array([[1-2*((j & r).bit_count()%2) for r in range(dimension)]
                      for j in range(dimension)])[:, m%dimension]
    clock = np.sqrt(np.log(n)/np.log(parent))
    normalized_frequency = clock[:, None] * np.log(parent[:, None]/m)
    test_input = np.zeros(dimension)
    test_input[:2] = (1/sqrt(2), -1/sqrt(2))
    totals = {}
    for name, angular_modes in curves.items():
        gram = np.zeros((dimension, dimension))
        binary = np.zeros_like(gram)
        windowed = {"equal": np.zeros_like(gram), "binary": np.zeros_like(gram)}
        for interp, multiplicity in angular_modes:
            statistics = "fermi" if name == "neutrino" else "photon"
            rows = np.array([amplitudes(index, m, interp, statistics)[1]
                             for index in parent])*np.sqrt(clock[:, None])
            signed = rows*signs
            gram += multiplicity*(rows@rows.T)
            binary += multiplicity*(signed@signed.T)
            for i in range(dimension):
                for j in range(i+1):
                    delta = normalized_frequency[i]-normalized_frequency[j]
                    overlap = np.exp(-.5*(16*delta)**2)
                    product = multiplicity*rows[i]*rows[j]*overlap
                    for key, value in (("equal", np.sum(product)),
                                       ("binary", np.sum(product*signs[i]*signs[j]))):
                        windowed[key][i, j] += value
                        if i != j:
                            windowed[key][j, i] += value
        totals[name] = dict(equal=gram, binary=binary, window=windowed)

    def summarize(mat):
        mean = np.trace(mat)/dimension
        eigenvalues = np.linalg.eigvalsh(mat)/mean
        return dict(difference_rate=float(test_input@mat@test_input/mean),
                    minimum=float(eigenvalues[0]), maximum=float(eigenvalues[-1]))
    report = {}
    for key, binary_species in (("none", ()), ("graviton_only", ("graviton",)),
                                ("all", tuple(curves))):
        raw = np.zeros((dimension, dimension))
        finite_time = np.zeros_like(raw)
        for name, matrices in totals.items():
            phase = "binary" if name in binary_species else "equal"
            raw += matrices[phase]
            finite_time += matrices["window"][phase]
        report[key] = dict(ideal=summarize(raw), gaussian=summarize(finite_time))
    assert report["all"]["gaussian"]["minimum"] > .94
    assert report["none"]["gaussian"]["difference_rate"] < 1e-5
    assert report["graviton_only"]["gaussian"]["minimum"] > .001
    return report


def massive_transmission(x, mu_over_T, ell, refinement):
    """Unit flux at the future horizon, Coulomb-distorted outgoing wave at infinity.

    Bound the outer-wave error by increasing its radius. The outgoing WKB
    amplitude preserves its q flux; using a massless outgoing plane wave at the
    outer boundary would give the wrong near-threshold flux.
    """
    k, mass = x/(4*pi), mu_over_T/(4*pi)
    q = np.sqrt((k-mass)*(k+mass))
    ll = ell*(ell+1)
    far = np.maximum(32., (32+ell)*refinement/q)
    f = 1-1/far
    short = ll/far**2+1/far**3
    p2 = q**2+mass**2/far-f*short
    local_wave = np.sqrt(p2)
    derivative_v = (mass**2+short)/far**2-f*(2*ll/far**3+3/far**4)
    outgoing = np.sqrt(q/local_wave).astype(complex)
    outer = (outgoing, outgoing*(1j*local_wave+f*derivative_v/(4*p2)))
    offset = 1e-7/refinement
    inner = (np.ones(k.shape, complex), -1j*k)

    def propagate(state, left, right, steps):
        amplitude, gradient = state
        step = (right-left)/steps
        offset_r = np.exp(left)
        advance = np.exp(step)
        midstep = np.sqrt(advance)
        def rhs(offset_r, y, v):
            radius = 1+offset_r
            barrier = offset_r/radius*(ll/radius**2+1/radius**3)-q*q-mass**2/radius
            return radius*v, radius*barrier*y
        for _ in range(steps):
            mid = offset_r*midstep
            end = offset_r*advance
            a, b = rhs(offset_r, amplitude, gradient)
            cc, d = rhs(mid, amplitude+step*a/2, gradient+step*b/2)
            e, ff = rhs(mid, amplitude+step*cc/2, gradient+step*d/2)
            g, h = rhs(end, amplitude+step*e, gradient+step*ff)
            amplitude = amplitude+step/6*(a+2*cc+2*e+g)
            gradient = gradient+step/6*(b+2*d+2*ff+h)
            offset_r = end
        return amplitude, gradient

    match = np.log(2.)
    logfar = np.log(far-1)
    steps = int(np.ceil(np.max(np.sqrt(q*q+mass**2/far)*far*(logfar-match))
                        *(6+2*refinement)))
    a, b = propagate(inner, np.log(offset), match, 600*refinement)
    cc, d = propagate(outer, logfar, match, steps)
    return 4*k*q/np.abs(a*d-b*cc)**2


def massive_scalar_power(mass, order, refinement):
    nodes, weights = np.polynomial.legendre.leggauss(order)
    xs, ws = [], []
    for low, high in [(0, 1), (1, 4), (4, 10), (10, 22), (22, 40)]:
        xs.extend(mass+(high+low)/2+(high-low)*nodes/2)
        ws.extend((high-low)*weights/2)
    x = np.array(xs)
    trans = massive_transmission(x, mass, 0, refinement)
    assert trans.min() >= 0 and trans.max() < 1.001
    return float(np.dot(ws, x*np.minimum(trans, 1)/np.expm1(x))/(128*pi**3))


def massive_check():
    powers = []
    for mass in (0, 2, 5, 10):
        coarse = massive_scalar_power(mass, 12, 1)
        fine = massive_scalar_power(mass, 24, 2)
        assert abs(coarse/fine-1) < .001
        powers.append(dict(mass_over_T=mass, s_wave_power_M2=fine,
                           refinement_change=abs(coarse/fine-1)))
    # Independent zero-mass radial equation and boundary series.
    x = np.arange(.03125, 36.01, .03125)
    trans = greybody(x/(4*pi), 0, 4, 0)
    baseline = simpson(np.r_[0., x*trans/np.expm1(x)], x=np.r_[0.,x])/(128*pi**3)
    assert abs(powers[0]["s_wave_power_M2"]/baseline-1) < .0005
    for row in powers:
        row["fraction_of_massless_s_wave"] = row["s_wave_power_M2"]/baseline
    scale = hbar*c**3/(8*pi*G*1e9*electron_volt)
    landmark = {name: scale/mass for name, mass in
                [("electron", .00051099895), ("muon", .1056584),
                 ("QCD_reference_0.2_GeV", .2), ("W_reference_80.4_GeV", 80.4)]}
    return dict(scalar=powers, temperature_GeV_times_mass_kg=scale, mass_kg_at_T=landmark)


def entropy_budgets(species):
    """Maximum single-mode entropy summed at the prescribed Hawking occupations.

    The fermion-state count describes the accessible spectrum of a stipulated
    theory and mass window. It is not a claim about the nature of neutrino mass.
    """
    budgets = {}
    for fermion_states in (0, 4, 6, 12):
        flux = {name: row["power_M2"]*(fermion_states/4 if name == "neutrino" else 1)
                for name, row in species.items()}
        total = sum(flux.values())
        cap = {name: weight/total*species[name]["maximum_mode_entropy_over_own_area_loss"]
               for name, weight in flux.items()}
        budgets[str(fermion_states)] = dict(by_species=cap, all_species=sum(cap.values()))
    assert abs(budgets["0"]["all_species"]-1.4847) < .001
    assert budgets["4"]["by_species"]["photon"] < 1
    return budgets


def relativistic_standard_model(species):
    """Free primary radiation at temperatures well above Standard Model masses.

    Count four real Higgs components, 45 Weyl fields and 12 gauge fields.
    The two transverse gravitational polarizations are separate. In this
    unbroken-theory benchmark, longitudinal gauge modes are not counted again.
    """
    x = np.arange(.0625, 36.01, .0625)
    grid = np.r_[0., x]
    scalar_flux = 0.
    for ell in range(6):
        coarse, fine = (greybody(x/(4*pi), ell, scale, 0) for scale in (2, 4))
        trans = fine+(fine-coarse)/15
        assert trans.min() > 0 and trans.max() < 1.00005
        integrand = x*(2*ell+1)*np.minimum(trans, 1)/np.expm1(x)
        scalar_flux += float(simpson(np.r_[0., integrand], x=grid))/(128*pi**3)
    weights = {"Higgs_components": 4*scalar_flux,
               "quarks": 72*species["neutrino"]["power_M2"]/4,
               "charged_leptons": 12*species["neutrino"]["power_M2"]/4,
               "active_neutrinos": 6*species["neutrino"]["power_M2"]/4,
               "gauge_polarizations": 24*species["photon"]["power_M2"]/2,
               "gravitons": species["graviton"]["power_M2"]}
    total = sum(weights.values())
    fractions = {key: value/total for key, value in weights.items()}
    assert abs(sum(fractions.values())-1) < 1e-14
    return dict(power_M2=weights, fraction=fractions, total_power_M2=total,
                real_scalar_power_M2=scalar_flux,
                graviton_fraction_three_right_handed_Weyl=weights["gravitons"]/(
                    total+6*species["neutrino"]["power_M2"]/4))


def run(amplitudes):
    species, curves = massless_species()
    return dict(massless=species, entropy_budgets=entropy_budgets(species),
                hot_minimal_standard_model=relativistic_standard_model(species),
                coherent_rates=inclusive_rates(curves, amplitudes),
                massive=massive_check())
