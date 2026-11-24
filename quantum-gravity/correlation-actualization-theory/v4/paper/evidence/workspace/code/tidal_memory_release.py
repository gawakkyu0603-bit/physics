"""Even-parity memory, a passive tidal receiver, and recoil of a radiating boundary.

Use r_s=1 for the wave equation and initial radius R_i=1 for the shell.
The only numerical ODE routines imported from Z.17 propagate the odd master field.
"""
import argparse
import json
from math import cos, log, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, simpson, solve_ivp
from scipy.optimize import brentq
from scipy.special import hyp2f1, spherical_jn

from fusion_surface_memory import propagate, start_at_horizon, start_at_infinity

ROOT = Path(__file__).resolve().parents[1]
RIM = 4 / 3


def superpotential(radius):
    return 4 + 1.5 * (1 - 1/radius) / (radius * (2*radius + 1.5))


def static_decay(radius):
    odd = hyp2f1(1, 5, 6, 1/radius) / radius**2
    odd_dx = 3*(1-1/radius)*odd/radius - 5/radius**3
    w = superpotential(radius)
    return (odd_dx+w*odd)/4, ((w-4)*(w+4)*odd+w*odd_dx)/4


def constants():
    d, gradient = static_decay(RIM)
    inertia = quad(lambda r: (static_decay(r)[0]/d)**2/(1-1/r),
                   RIM, np.inf, epsabs=2e-12)[0]
    cutoff = 10/d/(1/sqrt(2)+sqrt(.5+20*inertia/d))
    mass = 1/(sqrt(2)*cutoff)
    spring = cutoff/sqrt(2)
    lead = .5*quad(lambda r: r/(1+sqrt(r)), RIM, 1.5)[0]
    distance = lead/.5
    dx = lambda r: r-RIM + log((r-1)/(RIM-1))
    inner_reach = brentq(lambda r: dx(r)-distance, RIM, 1.5)
    fraction = (mass + quad(lambda r: (static_decay(r)[0]/d)**2/(1-1/r),
                            RIM, inner_reach)[0])/(mass+inertia)
    return dict(decay=d, robin=gradient/d, exterior_inertia=inertia,
                outgoing_coefficient=1/(9*d*d), cutoff=cutoff, mass=mass, spring=spring,
                near_field_overlap=static_decay(1.5)[0]/d, lead_time_rs=lead,
                uniform_flux_cap_fraction=(1-cos(lead/RIM))/2, causal_tube_edge_rs=inner_reach, accessible_kinetic_fraction=fraction)


def impedance(k, c, mass):
    spring = 5*mass / (c["decay"]*(mass+c["exterior_inertia"]))
    s = -1j*k
    b = c["robin"] + mass*s*s*(spring+s)/(mass*s*s+s+spring)
    loss = mass**2*k**5 / ((spring-mass*k*k)**2+k*k)
    assert np.max(np.abs(loss+b.imag)/(1+loss)) < 2e-14
    return b.real, loss


def response_grid(k, steps):
    off = .025
    far = np.maximum(14., 26/k)
    rim = np.log(RIM-1)
    a, da = propagate(start_at_horizon(k, 2, off, 2), k, 2, np.log(off), rim, steps//6, 2)
    h, dh = propagate(start_at_infinity(k, 2, far, 18, 2), k, 2, np.log(far-1), rim, steps, 2)
    horizon = 4*k*k/np.abs(a*dh-da*h)**2
    w = superpotential(RIM)
    even = (dh+w*h)/(4+1j*k)
    even_dx = (((w-4)*(w+4)-k*k)*h+w*dh)/(4+1j*k)
    return (even_dx/even).real, k/abs(even)**2, horizon


def independent_even_wave(k):
    # Integrate the polar potential itself with an adaptive solver. Only the
    # initial asymptotic normalization is shared with the odd-wave integration.
    far = max(14.,26/k)
    amp, grad = start_at_infinity(np.array([k]), 2, np.array([far]), 18, 2)
    w = superpotential(far)
    seed = np.array([(grad[0]+w*amp[0])/(4+1j*k),
                     (((w-4)*(w+4)-k*k)*amp[0]+w*grad[0])/(4+1j*k)])
    def equation(r, state):
        f = 1-1/r
        v_over_f = (24*r**3+12*r*r+9*r+2.25)/(r**3*(2*r+1.5)**2)
        return [state[1]/f, (v_over_f-k*k/f)*state[0]]
    wave = solve_ivp(equation, (far, RIM), seed, method="DOP853", rtol=5e-11, atol=1e-12)
    if not wave.success:
        raise RuntimeError(wave.message)
    y, dy = wave.y[:,-1]
    return (dy/y).real, k/abs(y)**2


def absorption(k, real, imag, c, mass):
    b_real, loss = impedance(k, c, mass)
    return 4*loss*imag / ((real-b_real)**2+(imag+loss)**2)


def optimal_envelope(k, real, imag, c):
    # xi = mass/(mass+I) maps every passive inertia onto the unit interval.
    # After cancelling xi^2, maximize transmission by minimizing
    # |A*xi+B+C/xi|^2. Every interior minimum solves the displayed quartic.
    inertia = c["exterior_inertia"]
    q = 5/c["decay"]
    z = real-c["robin"]+1j*imag
    a = q*(inertia*k*k-z)
    b = z*(q+1j*k-inertia*k*k)-1j*inertia*k**3
    d = -1j*k*z
    result = np.empty_like(k)
    for i, freq in enumerate(k):
        aa, bb, dd = a[i], b[i], d[i]
        roots = np.roots([abs(aa)**2, (aa*bb.conjugate()).real, 0,
                          -(bb*dd.conjugate()).real, -abs(dd)**2])
        points = [1.] + [r.real for r in roots if abs(r.imag)<1e-8 and 0<r.real<1]
        smallest = min(abs(aa*x+bb+dd/x)**2 for x in points)
        result[i] = 4*imag[i]*inertia**2*freq**5/smallest
    return result


def tidal_spectrum(c):
    probes = np.array([.002, .004, .008, .016, .04, .1, .2, .35, .5, .75, 1.])
    k = np.unique(np.r_[np.linspace(.001, .02, 25), np.linspace(.02, 3.5, 700),
                        np.geomspace(3.5, 12, 32), probes])
    coarse = response_grid(k, 1400)
    fine = response_grid(k, 2800)
    re, im, horizon = [b+(b-a)/15 for a, b in zip(coarse, fine)]
    flat_mass = c["mass"]
    absorbed = absorption(k, re, im, c, flat_mass)
    assert min(im)>0 and min(absorbed)>0 and max(absorbed)<=1+1e-9
    def power(prob):
        return simpson(k*prob/np.expm1(4*pi*k), x=k)
    normal = power(horizon)
    envelope = optimal_envelope(k, re, im, c)
    assert min(envelope-absorbed) > -2e-9
    envelope_coarse = optimal_envelope(k, coarse[0], coarse[1], c)
    def ratio(mass):
        return power(absorption(k, re, im, c, mass))/normal
    scan = np.geomspace(.001*flat_mass, 1000*flat_mass, 101)
    vals = [ratio(mass)-1 for mass in scan]
    fits = []
    for i in range(len(scan)-1):
        if vals[i]*vals[i+1] < 0:
            mfit = brentq(lambda m: ratio(m)-1, scan[i], scan[i+1])
            spec = absorption(k, re, im, c, mfit)
            band = (k >= .08) & (k <= .9)
            fits.append(dict(mass=mfit, relative_power=ratio(mfit),
                             largest_absolute_spectral_difference=float(max(abs(spec[band]-horizon[band])))))
    best_index = int(np.argmax(vals))
    memory = []
    for tau in [1, 5, 20]:
        density = 1/(k*(1+(tau*k)**2)**3)
        memory.append(dict(tau=tau, horizon=simpson(horizon*density, x=k),
                           surface=simpson(absorbed*density, x=k)))
    i = np.searchsorted(k, probes)
    sample = [dict(k=k[j], real_inertia=(re[j]-c["robin"])/k[j]**2,
                   imag_k5=im[j]/k[j]**5, horizon_k6=horizon[j]/k[j]**6,
                   surface_k6=absorbed[j]/k[j]**6, horizon=horizon[j], surface=absorbed[j])
              for j in i]
    direct_relative_errors = []
    for freq in [.04, .2, .75, 1.]:
        j = np.searchsorted(k, freq)
        alt_re, alt_im = independent_even_wave(freq)
        direct_relative_errors.append(max(abs(alt_re-re[j])/(1+abs(re[j])), abs(alt_im/im[j]-1)))
    assert max(direct_relative_errors)<2e-6
    assert abs(sample[0]["real_inertia"]/c["exterior_inertia"]-1) < .005
    assert abs(sample[0]["imag_k5"]/c["outgoing_coefficient"]-1) < .02
    assert abs(sample[0]["surface_k6"]/sample[0]["horizon_k6"]-1) < .01
    coarse_response = absorption(k, coarse[0], coarse[1], c, flat_mass)
    results = dict(samples=sample, direct_polar_max_error=max(direct_relative_errors), flat_power_over_horizon=ratio(flat_mass), power_matches=fits,
                   frequencywise_best_power_over_horizon=power(envelope)/normal,
                   envelope_resolution_change=abs(power(envelope)/normal-power(envelope_coarse)/power(coarse[2])),
                   coarse_frequency_grid_envelope_ratio=(simpson((k*envelope/np.expm1(4*pi*k))[::2], x=k[::2]) /
                                                         simpson((k*horizon/np.expm1(4*pi*k))[::2], x=k[::2])),
                   maximum_scanned_relative_power=1+vals[best_index], maximizing_sampled_mass=scan[best_index],
                   power_at_scan_ends=[vals[0]+1, vals[-1]+1], mass_search_interval=[scan[0], scan[-1]],
                   quadrupole_power_one_parity_G2M2=5*normal/(8*pi),
                   grid_max_abs_absorption_change=float(max(abs(absorbed-coarse_response))),
                   power_grid_change=abs(normal/power(coarse[2])-1),
                   memory_counts_per_squared_news=memory, k_integration_range=[float(k[0]),float(k[-1])],
                   sampled_max_transmission_per_energy=float(max(absorbed/k)))
    return results, (k, horizon, absorbed)


def energy_fraction(y):
    return y*(27-18*y+7*y*y)/32


def energy_slope(y):
    return (27-36*y+21*y*y)/32


def potential(y):
    f = energy_fraction(y)
    return (f-f*f/2)/sqrt(y)


def force_test(y):
    f = energy_fraction(y)
    return 2*y*(1-f)*energy_slope(y)-(f-f*f/2)


def emitted_mass(p):
    return .125+.5*energy_fraction(p)


def coordinate_time(rmin, rend, velocity, discharge, sign):
    # r=rmin+s^2 removes the square-root singularity at the simple bounce.
    def integrand(s, retarded):
        r = rmin+s*s
        speed = sqrt(max(velocity(r), 0.))
        proper = 2*s/speed
        if not retarded:
            return proper
        f = 1-2*discharge/r
        lapse = sqrt(f+speed**2)+sign*speed
        return proper/lapse
    return [quad(lambda s: integrand(s, retarded), 0, sqrt(rend-rmin),
                 epsabs=3e-9, epsrel=1e-9)[0] for retarded in (False, True)]


def trajectory(p):
    m = emitted_mass(p)
    mu = m/sqrt(p)
    top = brentq(force_test, 1.4, 1.7)
    turn_y = brentq(lambda y: potential(y)-mu, 1., top, xtol=3e-15)
    rmin = sqrt(p/turn_y)
    hit_y = brentq(lambda y: energy_fraction(y)/sqrt(y)-mu, .001, .7)
    rlast = sqrt(p/hit_y)
    def speed_squared(r):
        f = energy_fraction(p/r**2)
        return 2*m/r-2*f+f*f
    inward = coordinate_time(rmin, 1., speed_squared, m, -1)
    outward = coordinate_time(rmin, rlast, speed_squared, m, 1)
    v = sqrt(speed_squared(rlast))
    f = energy_fraction(hit_y)
    p_cross = 1-f+v
    assert abs(p_cross-1)<2e-12 and rmin>2*m and rlast>1
    drift = (2*hit_y*energy_slope(hit_y)-f)/rlast
    return dict(surviving_fraction=p, intermediate_mass=m, reduced_energy=mu,
                bounce_radius=rmin, smallest_exterior_f=1-2*m/rmin, final_radius=rlast,
                final_density=hit_y, speed_at_final_flash=v, final_lapse=p_cross,
                proper_time=sum((inward[0],outward[0])), retarded_time=inward[1]+outward[1],
                pre_bounce_proper=inward[0], timing_sensitivity=drift,
                leading_mass_per_time_error_squared=rlast*drift**2/2)


def terminal_flow(example):
    # A pressureless conversion phase locks P=1 after the expanding crossing.
    # This smooth finite-duration profile is an example, not a Hawking rate.
    r0, m0 = example["final_radius"], example["intermediate_mass"]
    duration = 2.
    def mass(t):
        s = t/duration
        return m0*(1-3*s*s+2*s**3)
    def radius(t):
        s = t/duration
        integrated = duration*m0*(s-s**3+s**4/2)
        return sqrt(r0*r0+2*integrated)
    rows = []
    for time in np.linspace(0, duration, 9):
        r, m = radius(time), mass(time)
        f = m/r
        v = f
        charge_fraction = (m/m0)**2
        energy_flux = m0*6*(time/duration)*(1-time/duration)/duration
        assert abs(r*(1-(1-f)**2+v*v)/2-m)<2e-15
        rows.append(dict(time=time, charge_fraction=charge_fraction, radius=r,
                         mass=m, luminosity=energy_flux, outgoing_lapse=1-f+v))
    assert abs(quad(lambda t: mass(t),0,duration)[0]-(radius(duration)**2-r0*r0)/2)<2e-15
    return dict(initial_radius_in_mass_units=r0/m0, duration=duration, samples=rows,
                final_radius=radius(duration), half_mass_hawking_added_R2_times_alpha_over_m04=15/32)


def shell():
    outer = brentq(force_test, .6, .9)
    inner = brentq(force_test, 1.4, 1.7)
    mu = lambda p: emitted_mass(p)/sqrt(p)
    lim1 = brentq(lambda p: mu(p)-potential(inner), .6, .85)
    lim2 = brentq(lambda p: mu(p)-potential(outer), .85, 1.)
    examples = [trajectory(p) for p in [.76, .8, .86, .9] if lim1<p<lim2]
    return dict(outer_barrier=[outer, potential(outer)], inner_barrier=[inner, potential(inner)],
                pulse_fraction_interval=[lim1, lim2], trajectories=examples,
                finite_duration_release=terminal_flow(next(row for row in examples if row['surviving_fraction']==.8)),
                static_last_flash_residual_fraction=1/3, dense_coexistence_y=9/7,
                coexistence_energy_per_defect=27/56)


def curved_rim(c):
    # Intrinsic meridional arclength s/L. The integrated Gaussian curvature
    # uses -rho'' ds dphi and stays finite at the regular poles.
    light_speed = 299792458.
    rs_time = 6*4.92549095e-6
    size = RIM*rs_time*light_speed
    waist = 10.
    beta = 1-waist/size
    rho_dd_times_L = lambda u: -np.sin(u)*(1+6*beta-9*beta*np.sin(u)**2)
    gaussian_cap = -2*pi*quad(rho_dd_times_L,0,pi/2)[0]
    assert abs(gaussian_cap-2*pi)<2e-14
    cap = c["uniform_flux_cap_fraction"]
    shear = 2*sqrt(2*size/waist-27/8)
    x = waist/size
    relative_area = (1+2*x)/3
    area_check = .5*quad(lambda u:np.sin(u)*(1-beta*np.sin(u)**2),0,pi)[0]
    assert abs(relative_area-area_check)<5e-15
    allowed = brentq(lambda t:6*t**3+15*t*t-8*t-4, 2/3, 1.)
    density_needed = relative_area*(1/x**2-.75)
    return dict(scale_m=size, sample_waist_m=waist, shape_beta=beta,
                curvature_at_waist_per_m2=-(3*beta-1)/(waist*size),
                integrated_cap_curvature=gaussian_cap, flux_phase_at_waist=-gaussian_cap/2,
                clock_budget_us=c["lead_time_rs"]*rs_time*1e6,
                spherical_readout_us=pi*size/light_speed*1e6, short_readout_us=pi*waist/light_speed*1e6,
                short_round_trip_us=2*pi*waist/light_speed*1e6,
                largest_round_cap_phase=2*pi*cap, diverted_in_round_cap=np.sin(pi*cap)**2,
                minimum_dimensionless_pressure_difference=shear, uniform_moving_min_radius_ratio=allowed,
                minimum_waist_density_over_uniform=density_needed)


def flat_cap():
    # Canonical radial master field. Delta-layer source at R on a regular flat slice.
    def transform(k, r):
        return 5*sqrt(2/pi)*spherical_jn(2,k*r)/k
    def check_quadrature(k, r):
        weight = quad(lambda s: (1-s*s)**2*np.cos(k*r*s), -1, 1, epsabs=1e-12)[0]
        return 5*sqrt(2/pi)*k*r*r*weight/16
    a, b = .6, 1.
    freq = np.linspace(.00001, 320., 32001)
    g = transform(freq, b)
    # These are finite-cutoff integrals. The analytic values also include the high-k tail.
    n = simpson(g*g,x=freq)
    energy = simpson((freq*g)**2,x=freq)
    spectral_error = max(abs(transform(k,r)-check_quadrature(k,r))
                         for k in [.02, .5, 1., 3., 9.] for r in [a,b])
    assert spectral_error<2e-13
    assert abs(n-10*b/21)<2e-6 and abs(energy-5/b)<.03
    sampled = []
    for k in [.01,.02,.04,.08]:
        single = transform(k, b)
        pair = transform(k,a)-(a/b)**2*single
        sampled.append(dict(k=k, one_density_over_k2=(single/k)**2,
                            compensated_density_over_k6=(pair/k**3)**2))
    lead = sqrt(2/pi)*a*a*(b*b-a*a)/42
    assert abs(sampled[0]["compensated_density_over_k6"]/lead**2-1)<1e-4
    def news_moments(x):
        w, wp, wpp = (1-x*x)**2, 4*x**3-4*x, 12*x*x-4
        return [wpp**2, wp**2, wp*wpp, wp*wp-w*wpp]
    moments = [quad(lambda x:news_moments(x)[j],-1,1)[0]*(5/16)**2 for j in range(4)]
    assert np.allclose(moments,[2.5,5/21,0,10/21],rtol=3e-14,atol=1e-15)
    return dict(outer_radius=b, inner_radius=a, energy_and_symplectic_integrals=moments, initial_norm=10*b/21, initial_stiffness=5/b,
                integrated_norm_to_320=n, integrated_stiffness_to_320=energy,
                transform_identity_max_error=spectral_error, samples=sampled,
                compensated_density_leading=lead**2, retarded_duration=2*b)


def draw(destination, grid, c, shells):
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MaxNLocator
    fig, (a,b) = plt.subplots(1, 2, figsize=(8.6, 3.15), layout="constrained")
    k, horizon, surface = grid
    ii = (k>=.08)&(k<=1.05)
    a.plot(k[ii], horizon[ii], color="#284f72", label="Schwarzschild horizon")
    a.plot(k[ii], surface[ii], "--", color="#a64e23", label="Tidal receiver")
    a.set(xlabel=r"Frequency $\omega r_s$", ylabel="Absorbed fraction", ylim=(-.015,1.06))
    a.legend(frameon=False, fontsize=8)
    ex = next(row for row in shells["trajectories"] if row["surviving_fraction"]==.8)
    m, rb, rl = ex["intermediate_mass"], ex["bounce_radius"], ex["final_radius"]
    for end, sign, label in [(1.,-1,"Contraction"),(rl,1,"Expansion")]:
        r = np.linspace(rb, end, 320)
        f = energy_fraction(.8/r**2)
        pp = 1-f+sign*np.sqrt(np.maximum(0,2*m/r-2*f+f*f))
        b.plot(r, pp, label=label, color="#284f72" if sign<0 else "#a64e23")
    b.axhline(1,color=".55",lw=.8)
    b.scatter([rl],[1],color="#242424",s=18,zorder=4)
    b.set(xlabel=r"Radius $R/R_i$",ylabel=r"Outgoing lapse $P=d\tau/du$")
    b.xaxis.set_major_locator(MaxNLocator(5))
    b.legend(frameon=False, fontsize=8)
    fig.savefig(destination)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path)
    args = parser.parse_args()
    c = constants()
    waves, grid = tidal_spectrum(c)
    shells = shell()
    report = dict(units="waves r_s=1; shell R_i=1", static_mode=c, scattering=waves, shell=shells, flat_cap=flat_cap(), geometric_rim=curved_rim(c))
    path = ROOT / "verification/tidal-memory-release-results.json"
    path.write_text(json.dumps(report, indent=2, allow_nan=False)+"\n", encoding="utf-8")
    if args.figure:
        draw(args.figure, grid, c, shells)
    print("Tidal material power / horizon:", waves["flat_power_over_horizon"])
    print("Last-flash trajectories:", shells["trajectories"])
