"""Galaxy and expansion tests for the charged layer action. Run from any directory."""
import io
import json
from itertools import product
from math import comb, exp, log, pi, sqrt
from pathlib import Path
from zipfile import ZipFile

import numpy as np
from scipy.constants import G, c, electron_volt, hbar
from scipy.special import j0
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
C_KMS = c / 1000.0
TRAP = np.trapezoid if hasattr(np, "trapezoid") else np.trapz


def read_sparc():
    with ZipFile(DATA / "sparc-rotmod-ltg.zip") as archive:
        curves = {Path(n).name.removesuffix("_rotmod.dat"): np.loadtxt(io.BytesIO(archive.read(n)))
                  for n in archive.namelist() if n.endswith("_rotmod.dat")}
    rows = {}
    for line in (DATA / "sparc-lelli2016c.mrt").read_text(encoding="ascii").splitlines():
        name = line[:11].strip()
        if name in curves:
            fields = line.split()
            # The authors' download separates the published fields with extra whitespace.
            assert fields[0] == name and len(fields) == 19
            rows[name] = (int(fields[4]), float(fields[5]), float(fields[11]), int(fields[17]))
    assert len(rows) == len(curves) == 175 and rows.keys() == curves.keys()
    return rows, curves


def annulus_weights(radius, lo, hi):
    """Integral of the piecewise-linear interpolant in log radius."""
    x = np.log(radius)
    l, h = np.log([lo, hi])
    assert x[0] <= l < h <= x[-1] and np.all(np.diff(x) > 0)
    left = np.maximum(x[:-1], l)
    right = np.minimum(x[1:], h)
    width = np.maximum(right - left, 0.0)
    right_weight = width * ((left + right) / 2 - x[:-1]) / np.diff(x)
    weights = np.zeros_like(x)
    weights[:-1] += width - right_weight
    weights[1:] += right_weight
    assert weights.min() > -1e-12 and abs(sum(weights) - (h - l)) < 1e-12
    return weights


def galaxies():
    catalog, curves = read_sparc()
    output, usable = {}, 0
    for name, (distance_method, inclination, rd, quality) in catalog.items():
        if inclination < 30 or quality > 2:
            continue
        usable += 1
        raw = curves[name]
        rows = raw[(raw[:, 0] > 0) & (raw[:, 1] > 0) & (raw[:, 2] > 0)]
        if len(rows) < 2 or rows[0, 0] > rd or rows[-1, 0] < 6 * rd or rd <= 0:
            continue
        r, speed, err = rows[:, :3].T
        components = rows[:, 3:6] * np.abs(rows[:, 3:6])
        weights = np.array([annulus_weights(r, rd, 2 * rd), annulus_weights(r, 3 * rd, 6 * rd)])
        observed = weights @ speed**2
        baryons = weights @ components
        f = 1 - (baryons @ [1, .5, .7]) / observed
        def lower_contrast(errors):
            olow = weights @ np.maximum(speed - errors*err, 0.0)**2
            ohigh = weights @ (speed + errors*err)**2
            if np.min(olow) <= 0:
                return None
            lower = []
            for disk, bulge in product((.3, .7), (.5, .9)):
                br = baryons @ [1, disk, bulge]
                hlo, hhi = br / olow, br / ohigh
                lower.append(min(hlo[0], hhi[0]) - max(hlo[1], hhi[1]))
            return float(min(lower))
        # Independent quadrature at interpolant endpoints checks analytic quadrature weights.
        for j, (lo, hi) in enumerate(((rd, 2*rd), (3*rd, 6*rd))):
            x = np.log(r)
            knots = np.r_[log(lo), x[(r > lo) & (r < hi)], log(hi)]
            check = TRAP(np.interp(knots, x, speed**2), knots)
            assert np.isclose(check, observed[j], rtol=1e-12)
        output[name] = dict(distance_method=distance_method, f_inner=float(f[0]), f_outer=float(f[1]),
                            contrast=float(f[1]-f[0]), conservative_contrast=lower_contrast(1),
                            conservative_3_errors=lower_contrast(3),
                            direct_sampling=bool(sum((r>=rd)&(r<=2*rd))>=2 and sum((r>=3*rd)&(r<=6*rd))>=2))
    def summarize(records):
        records = list(records)
        return dict(n=len(records), outer_larger=sum(r["contrast"] > 0 for r in records),
                    robust=sum(r["conservative_contrast"] > 0 for r in records),
                    robust_three=sum((r["conservative_3_errors"] or 0) > 0 for r in records),
                    median_inner=float(np.median([r["f_inner"] for r in records])),
                    median_outer=float(np.median([r["f_outer"] for r in records])),
                    median_contrast=float(np.median([r["contrast"] for r in records])),
                    negative_inner=sum(r["f_inner"] < 0 for r in records),
                    negative_outer=sum(r["f_outer"] < 0 for r in records))
    return dict(catalog=175, quality_inclination=usable, all=summarize(output.values()),
                distance_methods_2_to_5=summarize(r for r in output.values() if r["distance_method"] != 1),
                two_measured_in_each=summarize(r for r in output.values() if r["direct_sampling"]),
                per_galaxy=output)


def galaxy_and_expansion():
    mw = np.loadtxt(DATA / "milky-way-eilers-table1.txt")
    assert mw.shape == (38, 4)
    def potential(cut):
        r, v, *_ = mw[mw[:, 0] <= cut].T
        return float(TRAP(v*v, np.log(r))/C_KMS**2)
    expansion = {}
    for line in (DATA / "desi-dr2-bao-table-iv.txt").read_text(encoding="utf8").splitlines():
        if line.startswith("#") or line.startswith("BGS"):
            continue
        name, *values = line.split()
        z, dm, em, dh, eh, corr = map(float, values)
        def pull(f):
            return (dm - f*dh) / sqrt(em*em + f*f*eh*eh - 2*f*corr*em*eh)
        dust = 2*((1+z)**1.5 - (1+z))
        expansion[name] = dict(z=z, f_observed=dm/dh, f_dust=dust,
                               f_vacuum=z, dust_pull=pull(dust), vacuum_pull=pull(z))
    return dict(mw_rows=len(mw), mw_delta_phi_5_20=potential(19.71),
                mw_delta_phi_full=potential(24.82), mw_max_logmass_5_20=potential(19.71)/7,
                mw_vacuum_v2_relative_at_19_71=(75*.01971/201.91)**2, desi=expansion)


def particles_and_records():
    # Solar-neighbourhood density is the Eilers et al. fit. The speed and aperture are examples.
    mp = sqrt(hbar*c/(8*pi*G))
    one_mapped_mass = sqrt(pi)*mp
    rho = .30e9 * electron_volt/c**2 * 1e6
    geometric_per_s = (.5*rho / one_mapped_mass) * (pi*(5e-5)**2) * 220000
    eps = sqrt(7*.0017)
    mismatched = (1-eps**2)/2
    blank = float(j0(4))**2
    single = 1 - mismatched*(1-blank)
    n_gate = next(n for n in range(100) if single**n < .01)
    floor, n_coherent = 1., 0
    while floor >= .01:
        n_coherent += 1
        floor *= (2*n_coherent - 1)/(2*n_coherent)
    assert np.isclose(comb(2*n_gate, n_gate)/4**n_gate,
                      np.prod([(2*k-1)/(2*k) for k in range(1, n_gate+1)]))
    short = {}
    for hubble in (55, 65, 75):
        h = hubble*8/C_KMS
        eta = 24*h*h/(7+108*h*h)
        flux = 9 + 7/(12*h*h)
        assert np.isclose(2/eta, flux)
        short[str(hubble)] = dict(eta_upper=eta, k_over_M_lower=flux)
    warp = {str(length): dict(conservative_limit=bound, multiple=1/(7*bound),
                              maximum_single_fraction=sqrt(7*bound))
            for length, bound in ((.4,.013), (2.,.0038), (8.,.0017))}
    h04 = 65*.4/C_KMS
    return dict(force=1/7, warp_by_Mpc=warp,
                k_margin_for_0_4_Mpc_at_65=9+7/(12*h04*h04),
                min_range_Mpc_k1000_M16_at_65=C_KMS/65*sqrt(7/(12*(1000/16-9))),
                conservative_multiple=1/(7*.0017), epsilon_max=eps,
                fiducial_epsilon_max=sqrt(7*.00077), mismatch_min=mismatched, p_neutral_opposite=blank,
                independently_closed_pairs=n_gate, survival=single**n_gate,
                coherent_neutral_floor_at_n=comb(2*n_gate, n_gate)/4**n_gate,
                first_coherent_floor_below_one_percent=n_coherent,
                brane_antibrane_each_min_ug=4*one_mapped_mass*1e9,
                heavy_geometric_encounter_years=1/(geometric_per_s*365.25*86400),
                isocurvature_growth=(sqrt(1+24/7)-1)/4, short_range_8Mpc=short)


def cosmological_compensation():
    """Signed composition when particle numbers are conserved after production."""
    beta2 = 1/14
    beta = sqrt(beta2)
    norm = sqrt(63/2)
    duration = log(3400.)
    threshold = sqrt(7*.0017)
    def matter_limit(epsilon):
        start = np.arctanh(epsilon)
        def field(n, state):
            y, x, loss = state
            kfrac = x*x/(6*beta2)
            return [x, -(1-kfrac)*(1.5*x+3*beta2*np.tanh(y)), 1.5*x*x]
        sol = solve_ivp(field, (0.,duration), [start,0.,0.], method="DOP853",
                        rtol=2e-11, atol=1e-13)
        y, x, loss = sol.y
        energy = 3*beta2*(np.log(np.cosh(y))-np.log1p(-x*x/(6*beta2)))
        assert np.max(abs(energy+loss-energy[0])) < 5e-10
        assert np.max(abs(x)) <= 2*beta2+1e-10
        return float(np.tanh(y[-1]))
    critical = brentq(lambda e: matter_limit(e)-threshold, 0., .99)
    s = 1000/980
    v = brentq(lambda x: (1+8*x)/(1+x)**4 - s**6, 0, 1/6)
    eta = 4*v/3
    cterm, bterm = 4/3+eta, 1/3+2*eta
    matter_today = 3*eta/7
    def potential(Y):
        u = Y/norm
        terms = np.array([np.exp(-21*u), -cterm*np.exp(-18*u), bterm*np.exp(-9*u)])
        return sum(terms), float(terms @ [-21,-18,-9])/norm
    def run(epsilon, tolerance=3e-10):
        def sources(n, Y):
            a3 = np.exp(-3*n)
            r5 = (5/6)*matter_today*(1+epsilon)*a3*np.exp(beta*Y)/2
            r2 = (5/6)*matter_today*(1-epsilon)*a3*np.exp(-beta*Y)/2
            rr = matter_today*np.exp(-4*n)/3400
            rn = matter_today*a3/6
            V, grad = potential(Y)
            return r5, r2, rr, rn, V, grad
        def derivative(n, fields):
            Y, speed = fields
            r5, r2, rr, rn, V, grad = sources(n,Y)
            energy = (V+r5+r2+rr+rn)/(3-speed*speed/2)
            hprime = -speed*speed/2-(r5+r2+rn+4*rr/3)/(2*energy)
            return [speed, -(3+hprime)*speed-(grad+beta*(r5-r2))/energy]
        # Densities measured in units of F. a=1 is a reference epoch, not a fit to H0.
        sol = solve_ivp(derivative, (-duration,4.), [0.,0.], method="DOP853",
                        rtol=tolerance, atol=tolerance/200, dense_output=True)
        assert sol.success
        def snapshot(n):
            Y, speed = sol.sol(n)
            r5, r2, rr, rn, V, grad = sources(n,Y)
            energy = (V+r5+r2+rr+rn)/(3-speed*speed/2)
            return dict(u=float(Y/norm), eps=float((r5-r2)/(r5+r2)),
                        kinetic_fraction=float(speed*speed/6), vacuum_fraction=float(V/(3*energy)))
        # Independent conservation of all stress. Central differences of H^2.
        max_residual = 0.
        for n in np.linspace(-7.8,3.7,21):
            def h2(t):
                Y, speed = sol.sol(t)
                r5,r2,rr,rn,V,_ = sources(t,Y)
                return (r5+r2+rr+rn+V)/(3-speed*speed/2)
            Y, speed = sol.sol(n)
            r5,r2,rr,rn,V,_ = sources(n,Y)
            expected = -(r5+r2+rn+4*rr/3)-h2(n)*speed*speed
            numerical = (h2(n+1e-5)-h2(n-1e-5))/(2e-5)
            max_residual = max(max_residual, abs(numerical-expected)/h2(n))
        assert max_residual < 3e-6
        return dict(today=snapshot(0), future=snapshot(4), max_conservation_residual=max_residual)
    cases = {}
    for e in (-.9,-.6,-.3,-.1,0.,.1,.3,.6,.9):
        baseline = run(e)
        refined = run(e,6e-11)
        for epoch in ("today","future"):
            for field in ("u","eps","kinetic_fraction","vacuum_fraction"):
                assert abs(baseline[epoch][field]-refined[epoch][field]) < 3e-7
        # Residual of a finite difference is diagnostic and depends on floating-point libraries.
        cases[str(e)] = {k:baseline[k] for k in ("today","future")}
    # Endpoints adjacent to the exactly balanced solution, with the same homogeneous initial u.
    def first_crossing(sign):
        last = 0.
        def margin(e):
            return abs(run(e)["today"]["eps"]) - threshold
        for magnitude in np.linspace(.01,.5,50):
            current = sign*magnitude
            if margin(current) >= 0:
                return brentq(margin, min(last,current), max(last,current))
            last = current
        raise ValueError("No nearby composition threshold")
    edge_minus, edge_plus = first_crossing(-1), first_crossing(1)
    saddle = brentq(lambda y: potential(y)[1], .001, 2*norm)
    return dict(matter_only_eight_efolds={str(e):matter_limit(e) for e in (.1,.3,.6,.9,.95)},
                matter_only_initial_fraction_limit=critical, matter_only_exponent=(-1.5+sqrt(2.25-12*beta2))/2,
                eta=eta, u_vacuum_barrier=saddle/norm, reference_initial_epsilon_edges=[edge_minus,edge_plus],
                radiation_dust_vacuum_cases=cases)


def microscopic_checks():
    # ODE in x=sqrt(gamma)*(t-t0), z=(p^2+m_min^2)/gamma, hbar=c=1.
    modes = {}
    for z in (0.0, .3, 1.5):
        def vacuum(x):
            omega = sqrt(x*x+z)
            amplitude = 1/sqrt(2*omega)
            return np.array([amplitude, (-1j*omega-x/(2*omega**2))*amplitude])
        def rhs(x, y):
            return [y[1], -(x*x+z)*y[0]]
        occupations = []
        for edge in (14, 24):
            v, dv = solve_ivp(rhs, (-edge, edge), vacuum(-edge), t_eval=[edge],
                              method="DOP853", rtol=2e-10, atol=1e-12).y[:, -1]
            u, du = vacuum(edge)
            beta2 = abs(u*dv-du*v)**2
            alpha2 = abs(u.conjugate()*dv-du.conjugate()*v)**2
            assert abs(alpha2-beta2-1) < 2e-7
            occupations.append(float(beta2))
        expected = exp(-pi*z)
        assert abs(occupations[-1]-expected) < 3e-5
        modes[str(z)] = dict(occupations=occupations, analytic=expected)
    moment_states = {}
    for n in (1, 2, 10, 191):
        charges = np.array([-n, 0, n])
        weights = np.array([.5/n**2, 1-1/n**2, .5/n**2])
        assert np.isclose(weights @ charges, 0) and np.isclose(weights @ charges**2, 1)
        moment_states[str(n)] = dict(variance=float(weights@charges**2), blank=float(weights[1]),
                                     fourth_moment=float(weights@charges**4))
    return dict(passage=modes, equal_width_states=moment_states)


def dwarf_checks():
    # Wolf et al. Table 1. All dispersions hereafter are one-dimensional.
    pc = 3.085677581491367e16
    msun = 1.98847e30
    data = {"Draco": (291, 10.1, 2.11e7, 2.2e5), "Sculptor": (375, 9., 2.25e7, 2.5e6)}
    checks = {}
    for name, (r_pc, sig_kms, mass_solar, light_solar) in data.items():
        radius, dispersion = r_pc*pc, sig_kms*1e3
        rho = (mass_solar - .75*light_solar)*msun/(4*pi*radius**3/3)
        # Mean occupation <= 1 per species per cell after one parabolic vacuum passage.
        mass = (rho*6*pi**2*hbar**3/(2*5**1.5*dispersion**3))**.25
        checks[name] = dict(radius_pc=r_pc, sigma_star_kms=sig_kms, mass_half_solar=mass_solar,
                            total_light_solar=light_solar, min_mass_eV=mass*c*c/electron_volt,
                            min_mass_q_half_to_two_eV=[mass*c*c/electron_volt*q**(-.75) for q in (2,.5)],
                            max_decay_mediator_range_pc=r_pc*dispersion/c)
    return checks


def figure(sparc):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    _, curves = read_sparc()
    fig, ax = plt.subplots(1, 2, figsize=(8.0, 3.35), constrained_layout=True)
    mw = np.loadtxt(DATA / "milky-way-eilers-table1.txt")
    ax[0].errorbar(mw[:, 0], mw[:, 1], yerr=mw[:, 2:].T, fmt=".", ms=3.1, lw=.75,
                   label="Milky Way", color="#273b54")
    for name, color in (("NGC2403", "#a65828"), ("DDO154", "#147e81")):
        data = curves[name]
        ax[0].errorbar(data[:, 0], data[:, 1], yerr=data[:, 2], fmt=".", ms=2.7, lw=.65,
                       color=color, label=name)
        v2 = (data[:, 3:6] * np.abs(data[:, 3:6])) @ [1, .5, .7]
        ax[0].plot(data[:, 0], np.sqrt(np.maximum(v2, 0)), lw=1.05, color=color)
    ax[0].set(xlabel="Radius (kpc)", ylabel="Circular speed (km/s)", xlim=(0,26), ylim=(0,255))
    ax[0].legend(loc="lower left", bbox_to_anchor=(0,1.01), ncol=3,
                 columnspacing=.7, handletextpad=.25, borderaxespad=0, frameon=False, fontsize=7.5)
    points = list(sparc["per_galaxy"].values())
    for robust, col, label in ((False, "#a7a29b", "Other disks"), (True, "#147e81", "Positive throughout envelope")):
        group = [r for r in points if (r["conservative_contrast"] > 0) == robust]
        ax[1].scatter([r["f_inner"] for r in group], [r["f_outer"] for r in group], s=11,
                      color=col, alpha=.78, linewidths=0, label=label)
    vals = [r[k] for r in points for k in ("f_inner", "f_outer")]
    lo = min(-.05,min(vals)-.03)
    ax[1].plot([lo,1.02],[lo,1.02],lw=.9,color="#393e47", ls="--")
    ax[1].set(xlabel="Inner residual force fraction", ylabel="Outer residual force fraction",
              xlim=(lo,1.02), ylim=(lo,1.02))
    ax[1].legend(loc="lower right", frameon=False, fontsize=7)
    fig.savefig(ROOT / "manuscripts" / "galactic_wrapped_matter.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def main():
    sparc = galaxies()
    result = dict(sparc=sparc, distances=galaxy_and_expansion(), physics=particles_and_records(), dwarfs=dwarf_checks(), microscopic=microscopic_checks(), composition=cosmological_compensation())
    (ROOT/"verification"/"galactic-wrapped-matter-results.json").write_text(
        json.dumps(result, indent=2, allow_nan=False) + "\n", encoding="utf8")
    figure(sparc)
    print(json.dumps({k:v for k,v in sparc.items() if k!="per_galaxy"}, indent=2))
    print(json.dumps(result["distances"], indent=2))
    print(json.dumps(result["physics"], indent=2))
    print(json.dumps(result["dwarfs"], indent=2))


if __name__ == "__main__":
    main()
