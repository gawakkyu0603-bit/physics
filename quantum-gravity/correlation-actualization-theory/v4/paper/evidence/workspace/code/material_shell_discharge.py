"""Spherical self-gravity, recoil and electromagnetic lines of a charged surface.

Run with Python 3, NumPy and SciPy. Radii for the wave equation are in units
of 2GM. Shell trajectories instead use the initial radius 9GM/4. No fit or
random numbers enter. The result is written to verification/material-shell-discharge-results.json.
"""
import json
from math import exp, lgamma, log, log1p, pi, sqrt

import numpy as np
from pathlib import Path

from numpy.polynomial.legendre import leggauss
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import eval_jacobi, expit, hyp2f1, lpmv

Q = 2 / 3
Z = 1 / 3
R0 = 9 / 8
OMEGA0 = Z / R0
ALPHA = 1 / 137.035999
R_SUN_TIME = 2 * 4.92549095e-6
TIME_RADIUS = 3 * R_SUN_TIME * R0


def integral(fun, lo, hi):
    return quad(fun, lo, hi, epsabs=2e-10, epsrel=3e-10, limit=160)[0]


def recoil_limit(h):
    t = sqrt(h)
    return sqrt(t*t*(t+2)*(t**3+3*t+2)) / (t**3+t*t+t+3)


def daughters(h, j):
    """Rest actions as fractions of the static parent's conformal action."""
    q = ((1-h)*(1+h)+j*j)/2
    if not (0 < j < q < 1 and 0 < h < 1):
        raise ValueError((h, j))
    speed = sqrt((q-j)*(q+j)) / q
    a1 = (1-q)/h-h/3
    b1, b2 = h/3, j/3
    a2 = Z*q/j+b2
    c1 = 2*Q*((1-q)-h*h/3)
    c2 = 2*Q*(1-Q/2)
    coef = c2-2*a2*b2
    stationary = ((coef+sqrt(coef**2+32*a2**2*b2**2))/(4*a2**2))**(1/3)
    y_min = max(1, stationary)
    v2_min_sq = a2**2*y_min**2-1+coef/y_min+b2**2/y_min**4
    r = dict(remaining_action=h, emitted_action=j, local_energy=q,
             recoil=speed, upper_recoil=recoil_limit(h),
             emitted_adm=(1-c1/c2), minimum_outer_v_sq=v2_min_sq)
    minimum1 = (2*b1/a1)**(1/3)
    # Evaluate the cubic at its minimum using a series around y=1 to keep
    # the two nearly coincident turning points resolved for a large parent.
    gap_at_one = (q*speed/h)**2/(sqrt(1+(q*speed/h)**2)+1)

    def rest_gap(y):
        u = y-1
        return gap_at_one + u*((a1-2*b1)+b1*u*(3+2*u)/(y*y))

    if rest_gap(minimum1) >= 0 or v2_min_sq <= 0:
        return r
    yb = brentq(rest_gap, minimum1, 1, xtol=1e-15)
    delta = 1-yb
    r["bounce_radius"] = yb
    r["radius_over_inner_schwarzschild"] = yb/c1

    def v1_factored(y, distance):
        # Difference of the functions at y and at the outer turning root.
        slope = a1-b1*(y+yb)/(y*y*yb*yb)
        return sqrt(distance*slope*(a1*y+b1/y**2+1))

    def delay_leg(s):
        y = yb+delta*s*s
        scaled_v = v1_factored(y, delta)
        return 2*delta*(a1*y-b1/y**2)/((1-c1/y)*scaled_v)

    def outward1(x):
        y = 1/x
        v = v1_factored(y, y-yb)
        return 1/(x*x*v*(a1*y-b1/y**2+v))

    def outward2(x, sign):
        y = 1/x
        v = sqrt(a2*a2*y*y-1+coef/y+b2*b2/y**4)
        return 1/(x*x*v*(a2*y+sign*b2/y**2+v))

    u1 = 2*integral(delay_leg, 0, 1)+integral(outward1, 0, 1)
    u2 = integral(lambda x: outward2(x, 1), 0, 1)
    r.update(middle_arrival_lag=u1-u2, outer_bondi_delay=integral(
             lambda x: outward2(x, -1), 0, 1), no_recross=u1>u2)
    return r


def harmonic(l, m, x):
    if m < 0:
        return (-1)**(-m)*harmonic(l, -m, x)
    norm = sqrt((2*l+1)/(4*pi))*exp((lgamma(l-m+1)-lgamma(l+m+1))/2)
    return norm*lpmv(m, l, x)


def bright_current(d, angular, nodes):
    # Adjacent scalar harmonics with opposite particle charges.
    left = (d-2)//2
    right = d//2
    assert d == left+right+1 and 1 <= angular <= left+right
    x, weights = leggauss(nodes)
    deriv_p = (angular+1)*eval_jacobi(angular-1, 1, 1, x)/2
    prefactor = (2*pi*sqrt((2*angular+1)/(4*pi))
                 /sqrt(angular*(angular+1)*(left+.5)*(right+.5)))
    values = [prefactor*m*np.dot(weights, deriv_p*harmonic(left, m, x)
                                 *harmonic(right, -m, x))
              for m in range(-left, left+1)]
    return float(np.dot(values, values))


def outgoing(d, angular, cutoff, tolerance):
    """Outgoing unit-Wronskian-amplitude wave integrated in r, not r_*."""
    ell = angular*(angular+1)
    omega = d*OMEGA0

    def rhs(r, a):
        f = 1-1/r
        return [a[1]/f, (ell*f/r**2-omega**2)*a[0]/f]

    f = 1-1/cutoff
    v = ell*f/cutoff**2
    vx = f*ell*(3-2*cutoff)/cutoff**4
    k = sqrt(omega**2-v)
    amp = sqrt(omega/k)
    init = [complex(amp), amp*(1j*k+vx/(4*k*k))]
    sol = solve_ivp(rhs, (cutoff, R0), init, method="DOP853",
                    rtol=tolerance, atol=tolerance*0.05)
    if not sol.success:
        raise RuntimeError(sol.message)
    amp, deriv = sol.y[:, -1]
    log_deriv = deriv/amp
    ray2 = 1-ell/d**2
    wave = (abs(log_deriv)**2+omega**2*ray2)/(2*omega*log_deriv.imag)
    wronskian_error = abs((amp.conjugate()*deriv).imag/omega-1)
    return float(wave), float(abs(deriv/OMEGA0)**2), float(wronskian_error)


def infall_clocks():
    # A signals radially inward from the photon sphere. Ingoing EF time of
    # the signal is constant. The static B receiver beats the object.
    start = 1.5
    delta_v = integral(lambda r: r/(1+sqrt(r)), R0, start)
    w = Z*delta_v/R0
    return dict(infall_from_photon_sphere_us=3*R_SUN_TIME*(2/3)*start**1.5*1e6,
                v_advance_rs=delta_v, surface_window=w,
                surface_advance_us=w*TIME_RADIUS*1e6, max_arc_m=w*TIME_RADIUS*299792458)


def cap_test(d, j):
    nodes, weights = leggauss(max(48,j+3))
    def cap(theta, details=False):
        a = 2*np.sin(theta/2)**2
        x = 1-a*(nodes+1)/2
        sin_sq = (1-x)*(1+x)
        entries = []
        for m in range(j+1):
            f = harmonic(j, m, x)
            prev = harmonic(j-1,m,x) if m<j else 0
            deriv = sqrt((j*j-m*m)*(2*j+1)/(2*j-1))*prev-j*x*f
            prob = pi*a/(j*(j+1))*np.dot(weights,(deriv**2+m*m*f*f)/sin_sq)
            entries.append(float(prob))
        assert abs((entries[0]+2*sum(entries[1:]))/(2*j+1)-a/2) < 2e-12
        ratio = min(entries)/max(entries)
        # For each magnetic label exact capture needs d*T*(sqrt(u)+u)>=1.
        # Eliminating the common multiplier gives a necessary anisotropy test.
        needed = (2/(d*theta*(sqrt(1+4/(d*theta))+1)))**2
        if not details:
            return min(1,entries[-1]/(a/2))-needed
        viable=[m for m,val in enumerate(entries) if d*theta>=pi/2 and val>=needed*max(entries)]
        modes=sum(1 if m==0 else 2 for m in viable)
        return dict(eligible_abs_m=viable, eligible_modes=modes,
                    one_photon_time_modes_lower=((2*j+1+modes-1)//modes if modes else None),
                    cap_fraction=a/2, extreme_M_fraction=entries[-1],
                    min_over_max=ratio, required_min_over_max=needed,
                    monotone_ratio_upper=min(1,entries[-1]/(a/2)))
    w = infall_clocks()["surface_window"]
    critical = brentq(cap,w,pi/2)
    time = max(critical,pi/(2*d))
    seed = brentq(lambda r: Z/R0*integral(lambda s: s/(1+sqrt(s)),R0,r)-time,
                  R0,20)
    return dict(d=d, J=j, **cap(w,True), necessary_surface_time=time,
                earliest_signal_radius_bound_rs=seed,
                bright_speed_time=pi/(2*d))


def spectral_data(d, angular, current):
    # Static decaying Maxwell solution F=r^{-J} 2F1(J,J+2;2J+2;1/r).
    # Its inward logarithmic derivative gives the exact integral of |g|^2/nu.
    j = angular
    x = 1/R0
    h = hyp2f1(j,j+2,2*j+2,x)
    hp = j*(j+2)/(2*j+2)*hyp2f1(j+1,j+3,2*j+3,x)
    slope = Z**2/R0*(j+x*hp/h)
    mass_fraction = 4*pi*ALPHA*current*OMEGA0/(2*d*slope)
    radial_ratio = j+x*hp/h
    # Independent evolution of the static logarithmic derivative in log(r).
    def radial(log_r, y):
        inverse_r = exp(-log_r)
        f = 1-inverse_r
        return [y[0]**2+(1-inverse_r/f)*y[0]-j*(j+1)/f]
    far = 5000
    ode = solve_ivp(radial,(log(far),log(R0)),
                    [j+j*(j+2)/(2*j+2)/far],
                    method="DOP853",rtol=1e-10,atol=1e-11)
    assert ode.success and abs(ode.y[0,-1]/radial_ratio-1)<2e-9
    assert 0<mass_fraction<4*pi*ALPHA*current/(2*d*Z*j)<1
    duration = infall_clocks()["surface_window"]*d
    amplitude_floor = max(0,1-duration*(sqrt(mass_fraction)+mass_fraction))
    return dict(threshold_shift_over_gap=mass_fraction,
                finite_capture_upper=1-amplitude_floor**2,
                static_green_residual=abs(ode.y[0,-1]/radial_ratio-1))


def line(d, angular, double=False):
    current = bright_current(d, angular, 80)
    xi, impedance, err = outgoing(d, angular, 70, 8e-10)
    ray = sqrt(1-angular*(angular+1)/d**2)
    row = dict(d=d, J=angular, ray_recoil=ray, stress_recoil=xi,
               bright_current_sq=current, wronskian_error=err,
               gamma_conformal=2*(4*pi*ALPHA)*d*current/impedance,
               omega_over_T_H=4*pi*d*OMEGA0,
               above_escape_ray=ray>sqrt(11/27),
               below_recoil_limit=xi<1/sqrt(2))
    row.update(spectral_data(d, angular, current))
    assert xi >= ray-2e-11 and current > 1e-15 and err < 5e-7
    if double:
        other, other_z, _ = outgoing(d, angular, 140, 9e-11)
        row["cutoff_change_recoil"] = abs(xi-other)
        row["cutoff_relative_change_rate"] = abs(impedance/other_z-1)
        row["current_order_check"] = abs(current-bright_current(d,angular,110))
        assert row["cutoff_change_recoil"] < 4e-6
        assert row["cutoff_relative_change_rate"] < 1e-5
    return row


def hawking_budget(d,j):
    # Number flux of one axial J multiplet in the standard neutral, isolated
    # Schwarzschild spectrum. The greybody probability is bounded above by 1.
    # This lower bound on total luminosity is below Page's photon contribution
    # 3.3638e-5 alone. Other species can shorten the lifetime further.
    alpha_min = 3.30e-5
    x_min = 4*pi*d*OMEGA0
    modes = 2*j+1
    n_per_mass_sq = modes*(-log1p(-exp(-x_min)))/(32*pi*pi*alpha_min)
    critical_mass = sqrt((1-1/modes)/n_per_mass_sq)
    late_mean=n_per_mass_sq*(1e6/2.176434e-8)**2
    vacuum=max(0,1-late_mean)
    blank_amplitude=1/modes
    overlap=vacuum*blank_amplitude+sqrt(late_mean*(2-late_mean)*(1-blank_amplitude**2))
    return dict(d=d,J=j, x_min=x_min, luminosity_floor=alpha_min,
                max_photons_per_delta_mass_sq=n_per_mass_sq,
                critical_mass_planck=critical_mass,critical_mass_kg=critical_mass*2.176434e-8,
                avg_photons_upper_from_1e6kg=late_mean,
                max_fresh_entanglement_fidelity_from_1e6kg=overlap**2,
                max_early_infidelity_for_exact_recovery=late_mean*(2-late_mean))


def cross_checks():
    balances = []
    for h in (.16,.47,.85,.97):
        for j in (.18*(1-h), .65*(1-h), .85*(1-h)):
            row = daughters(h,j)
            q, p = row["local_energy"], row["local_energy"]*row["recoil"]
            c1 = 2*Q*(1-q-h*h/3)
            c2 = 2*Q*(1-Q/2)
            v1, v2 = -p/h, Z*p/j
            m1 = h*(sqrt(1+v1*v1)-h/3)
            gap = j*(sqrt(1-c1+v2*v2)-j/3)
            balances += [abs(m1+gap-(1-Q/2)),
                         abs(sqrt(1-c1+v1*v1)-sqrt(1+v1*v1)+Q*h),
                         abs(sqrt(1-c2+v2*v2)-sqrt(1-c1+v2*v2)+Q*j)]
    assert max(balances)<2e-13
    # Exact azimuthal current for l=2,3 to J=4 by polynomial integration.
    current_error = abs(pi*bright_current(6,4,80)-1/7)
    assert current_error<3e-14
    return dict(vertex_max_residual=max(balances), junction_preparations=12,
                low_line_current_pi_error=current_error)


def draw_figure(data,path):
    import matplotlib
    matplotlib.use("Agg")
    from matplotlib import pyplot as plt
    plt.rcParams.update({"font.size":9,"axes.spines.top":False,"axes.spines.right":False,
                         "pdf.fonttype":42})
    fig,(force,cap)=plt.subplots(1,2,figsize=(7.15,2.8),layout="constrained")
    rows=[r for r in data["axial_maxwell"] if r["d"] in (6,14,20,26,30)]
    xx=list(range(len(rows)))
    force.axhspan(sqrt(11/27),1/sqrt(2),color="#deeae3",label="Two-shell ray window")
    for i,row in enumerate(rows):
        force.plot([i,i],[row["ray_recoil"],row["stress_recoil"]],color="#71808a",lw=1.2)
    force.scatter(xx,[r["ray_recoil"] for r in rows],facecolors="white",
                  edgecolors="#263e58",zorder=3,label="Ray")
    force.scatter(xx,[r["stress_recoil"] for r in rows],color="#994422",marker="D",
                  s=18,zorder=4,label="Wave stress / flux")
    force.set(xticks=xx,xticklabels=[f'{r["d"]}, {r["J"]}' for r in rows],
              ylim=(.60,1.25),xlabel="Energy gap d, photon angular momentum J",
              ylabel="Radial momentum per unit energy",title="Emission at the surface")
    force.legend(frameon=False,fontsize=7,loc="upper right")
    rows=data["cap_constraints"]
    xx=list(range(len(rows)))
    for i,r in enumerate(rows):
        cap.plot([i,i],[r["min_over_max"],r["required_min_over_max"]],color="#85969e",lw=1.2)
    cap.scatter(xx,[r["min_over_max"] for r in rows],color="#254a68",s=25,label="Available eigenvalue ratio")
    cap.scatter(xx,[r["required_min_over_max"] for r in rows],color="#994422",
                marker="D",s=20,label="Required for full capture")
    cap.set(xticks=xx,xticklabels=[f'{r["d"]}, {r["J"]}' for r in rows],
            yscale="log",yticks=[1e-50,1e-40,1e-30,1e-20,1e-10,1],
            ylim=(1e-54,1e6),xlabel="Energy gap d, photon angular momentum J",
            ylabel="Weakest / strongest response",title="Acquisition from the photon sphere")
    cap.legend(frameon=False,fontsize=7,loc="lower left")
    fig.savefig(path,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    branches = [dict(parent=parent, **daughters(1-6/parent,sqrt(20)/parent))
                for parent in (12,24,60,120,600,6000,60000)]
    lines = [line(d, j, double=(d<=12 or d==30)) for d,j in
             ((4,2),(6,4),(8,6),(10,6),(10,8),(12,8),(14,10),
              (16,12),(18,12),(18,14),(20,14),(22,16),(24,18),
              (26,18),(28,20),(30,22),(32,24),(34,24),(38,28))]
    # A standing gas of two-component surface Dirac fields, zero chemical
    # potential, with both particle signs. Conformal surface energies n/R.
    tw = R0/(4*pi*Z)
    kt = sum(4*n*n*expit(-n/tw) for n in range(1,100))
    radius_m = TIME_RADIUS*299792458
    kstar = Q*(radius_m/1.616255e-35)**2
    assert all(r["emitted_adm"]>0 for r in branches)
    assert any(r.get("no_recross",False) for r in branches)
    assert any(r["above_escape_ray"] and r["below_recoil_limit"] for r in lines)
    caps = [cap_test(d,j) for d,j in ((6,4),(20,14),(26,18),(30,22))]
    return dict(hawking_count=[hawking_budget(20,14),hawking_budget(26,18)],
                independent_checks=cross_checks(), causal_clocks=infall_clocks(), cap_constraints=caps, static=dict(radius_m_3solar=radius_m,
                radius_time_s=TIME_RADIUS, thermal_T_R=tw,
                thermal_action_per_Dirac=kt, needed_action_3solar=kstar,
                degenerate_highest_level=(3*kstar/4)**(1/3),
                radial_last_adm_fraction=.75,
                escape_recoil=sqrt(11/27), small_release_max=1/sqrt(2)),
                sf_split_d6_J4=branches, axial_maxwell=lines)


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",help="Also write the two-panel PDF to this path")
    args=parser.parse_args()
    data=main()
    if args.figure:
        draw_figure(data,args.figure)
    target=Path(__file__).resolve().parents[1]/"verification"/"material-shell-discharge-results.json"
    target.write_bytes((json.dumps(data,indent=2,sort_keys=True,allow_nan=False)+"\n").encode("utf8"))
    print(target.name)
