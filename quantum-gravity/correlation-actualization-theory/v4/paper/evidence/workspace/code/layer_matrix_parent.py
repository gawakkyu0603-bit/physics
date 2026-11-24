"""Finite-rank matrix receipts and the compactified, reference-preserving output.

Matrix units absorb the DLCQ radius and the eleven-dimensional Planck length.
The independent four-dimensional scattering solver is supplied with Paper 4.
"""
import argparse
import json
from math import exp, log, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.interpolate import PchipInterpolator
from scipy.optimize import brentq

from energy_matched_matrix_receipts import calculate as energy_matched_receipts
from fusion_surface_memory import greybody

ROOT = Path(__file__).resolve().parents[1]
SIGMA = (np.array([[0, 1], [1, 0]], complex),
         np.array([[0, -1j], [1j, 0]], complex), np.diag([1., -1.]))
ID = np.eye(2)


def tensor(factors):
    item = np.ones((1, 1), complex)
    for factor in factors:
        item = np.kron(item, factor)
    return item


def clifford_nine():
    gamma = []
    for site in range(4):
        for pauli in SIGMA[:2]:
            gamma.append(tensor([SIGMA[2]]*site+[pauli]+[ID]*(3-site)))
    gamma.append(tensor([SIGMA[2]]*4))
    for i, a in enumerate(gamma):
        for j, b in enumerate(gamma):
            np.testing.assert_allclose(a@b+b@a, 2*np.eye(16)*(i == j), atol=1e-14)
    return gamma


def spin(size):
    j = (size-1)/2
    m = np.arange(size)-j
    raising = np.diag(np.sqrt((j-m[:-1])*(j+m[:-1]+1)), -1)
    return [(raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(m)]


def localizers():
    gamma = clifford_nine()
    chi = -1j*gamma[0]@gamma[1]@gamma[2]
    rng = np.random.default_rng(142)
    tables = []
    for size in (2, 3, 4, 7, 12):
        j = (size-1)/2
        matrices = spin(size)
        basis, _ = np.linalg.qr(rng.normal(size=(size, size))+1j*rng.normal(size=(size, size)))
        for scaled_radius in (.65, 1.15):
            a = [x.copy() for x in matrices]
            a[2] = a[2]-j*scaled_radius*np.eye(size)
            def make(cliff, xs):
                return sum(np.kron(pauli, x) for pauli, x in zip(cliff, xs))
            little = make(SIGMA, a)
            expect = int(scaled_radius < 1)
            assert np.sign(np.linalg.eigvalsh(little)).sum()/2 == expect
            big = make(gamma[:3], a)
            eig, vec = np.linalg.eigh(big)
            chirality = np.kron(chi, np.eye(size))
            orient = np.real(np.diag(vec.conj().T@chirality@vec))
            index = float(orient@np.sign(eig)/16)
            assert abs(index-expect) < 2e-12 and np.sum(np.sign(eig)) == 0
            rotated = make(SIGMA, [basis@x@basis.conj().T for x in a])
            np.testing.assert_allclose(np.linalg.eigvalsh(rotated), np.linalg.eigvalsh(little),
                                       rtol=1e-12, atol=1e-13)
            gapped = big+.3*np.kron(gamma[3], np.eye(size))
            np.testing.assert_allclose(gapped@gapped, big@big+.09*np.eye(16*size),
                                       atol=3e-13)
            tables.append(dict(size=size, radius_over_alpha_j=scaled_radius,
                               signed_total=int(np.sum(np.sign(eig))), relative_index=index))
    return tables


def dynamical_crossing():
    # For H=(v*t)*sigma_z+b*sigma_x, start in the instantaneous negative band.
    rows = []
    for b in (0., .35, .70, 1.):
        def excitation(limit):
            def h(t):
                return np.array([[t, b], [b, -t]])
            initial = np.linalg.eigh(h(-limit))[1][:,0].astype(complex)
            out = solve_ivp(lambda t,y: -1j*h(t)@y, (-limit,limit), initial,
                            method="DOP853",rtol=2e-10,atol=2e-12)
            assert out.success
            final = np.linalg.eigh(h(limit))[1][:,1]
            return float(abs(np.vdot(final,out.y[:,-1]))**2)
        exact = exp(-pi*b*b)
        finite = [excitation(t) for t in (18., 27.)]
        assert abs(finite[-1]-exact)<1.2e-4
        rows.append(dict(normal_gap=b, sweep=1., diabatic=exact, finite_window=finite))
    ratio = .75
    time = quad(lambda z: 1/sqrt(1-z**4),ratio,1,epsabs=2e-12)[0]
    sol = solve_ivp(lambda t,y:(y[1], -2*y[0]**3),[0,time],(1.,0.),
                    method="DOP853",rtol=2e-12,atol=3e-14)
    assert abs(sol.y[0,-1]-ratio)<1e-11
    return dict(crossing_time_times_alpha0=time,
                slope_per_j_alpha0_squared=sqrt(1-ratio**4),landau_zener=rows)


def logical_outcomes():
    # Input: unknown state of A, possibly entangled with an external qubit.
    # A received sign controls which physical port carries both its rails.
    rng = np.random.default_rng(49)
    state = rng.normal(size=4)+1j*rng.normal(size=4)
    state = state/np.linalg.norm(state)
    state = state.reshape(2,2)
    prob = (0.19, 0.81)
    swap = np.array([[0,1],[1,0]],complex)
    full = np.kron((ID-swap)/2,np.eye(2))
    np.testing.assert_allclose(np.eye(4)-2*full,np.kron(swap,ID),atol=1e-14)
    # Two material encounters. For every history the pulled-back effect is scalar.
    unitaries = (ID, SIGMA[0])
    for i in range(2):
        for j in range(2):
            k = sqrt(prob[i]*prob[j])*unitaries[j]@unitaries[i]
            np.testing.assert_allclose(k.conj().T@k,prob[i]*prob[j]*ID,atol=1e-14)
            decoded = (k.conj().T@k@state)/(prob[i]*prob[j])
            np.testing.assert_allclose(decoded,state,atol=1e-14)
    # Two individually fair external marks, whose XOR records the logical basis.
    have = np.zeros((2,2,2))
    for bit in range(2):
        for first in range(2):
            have[bit,first,first^bit]=.5
    assert np.allclose(have.sum(axis=1),.5) and np.allclose(have.sum(axis=2),.5)
    hidden_overlap = float(np.sqrt(have[0]*have[1]).sum())
    return dict(two_mark_overlap=hidden_overlap, lost_bell_fidelity=(1+hidden_overlap)/2,
                origin_preserved_bell_fidelity=1.)


def compactified_emission():
    # Each polarization has two orthogonal chiral absorption contractions.
    grid = np.arange(0,30+.03125,.0625)
    x = grid[1:]
    c, f = (greybody(x/(4*pi), 0, scale, 0) for scale in (2,4))
    t = np.clip(f+(f-c)/15,0,1)
    curve = PchipInterpolator(grid,np.r_[0.,t])
    def bare(x):
        return x**3/(16*pi**2*np.tanh(x/4))
    root = brentq(lambda x: bare(x)-1.,3.,8.)
    samples = [dict(x=v, bare_transmission=bare(v), exterior_transmission=float(curve(v)))
               for v in (.5,1,2,4,6,8)]
    masses = (1., 1.35, .72, 1/(64*1.35*.72))
    # G_4=1 and momentum mass 1/R = m4. The radius product has no adjustable factor.
    mass = 2e4
    n = mass/(8*np.array(masses[:3]))
    radius = 64*np.prod(n)/masses[-1]
    level = radius*mass/8
    assert abs(radius/(8*mass**3)-1)<1e-12 and abs(level/mass**4-1)<1e-12
    # Track the same tagged harmonic adiabatically while W follows the neutral saddle.
    hot = .004387533623142378
    page = .00016366608457660264+.00003363854531058362+.000003836739731333932
    rows = []
    for label, luminosity in (("Page_content",page),("relativistic_SM",hot)):
        for ratio in (.99,.9,.8):
            def hazard(start_x):
                return quad(lambda z: float(curve(start_x/z**2))*np.tanh(start_x/(4*z**2))/z,
                            ratio,1,epsabs=2e-9,limit=120)[0]/(8*pi*luminosity)
            low, high = hazard(2), hazard(4)
            p_two = 1-(4*exp(-low)-exp(-4*low))/3
            p_one = -np.expm1(-high)
            rows.append(dict(content=label,final_mass_fraction=ratio,low_hazard=low,
                             high_hazard=high,one_complete=float(p_one),two_complete=p_two,
                             cross_phase_amplitude=sqrt(max(0,p_one*p_two)),
                             exact_heralded_rate=min(p_one,p_two)))
    return dict(bare_unitarity_limit=root,samples=samples,finite_release=rows,
                frozen_temperature_ratio_after_tenth=.9*sqrt(.6))


def four_dimensional_probe():
    # Compactified matrix string: three adjoint generators and one circle.
    spectra = []
    for size in (2, 4, 7, 12):
        ident = np.eye(size)
        actions = [np.kron(y,ident)-np.kron(ident,y.T) for y in spin(size)]
        casimir = sum(a @ a for a in actions)
        levels = np.concatenate([np.full(2*l+1, l*(l+1)) for l in range(size)])
        err = float(np.max(abs(np.linalg.eigvalsh(casimir)-levels)))
        assert err < 5e-12
        spectra.append(dict(rank=size,dimension=size**2,spectrum_error=err))
    rows = []
    for rank, diffusion in ((12,.01),(32,.01),(64,.01),(128,.01),(128,.003)):
        # Frozen alpha=1, circle length 2*pi; truncate Fourier terms past exp(-64).
        n = np.arange(-int(np.ceil(8/np.sqrt(diffusion))),int(np.ceil(8/np.sqrt(diffusion)))+1)
        l = np.arange(rank)
        w = (2*l+1)*np.exp(-diffusion*l*(l+1))
        v = np.exp(-diffusion*n*n)
        dimension = 2*diffusion*(w @ (l*(l+1))/w.sum()+v @ (n*n)/v.sum())
        rows.append(dict(rank=rank,diffusion=diffusion,spatial_spectral_dimension=float(dimension)))
    assert abs(rows[-1]["spatial_spectral_dimension"]-3)<.003
    for alpha, velocity in ((1.,0.),(.75,-np.sqrt(1-.75**4))):
        curvature_base = (-2*alpha**3*alpha-velocity**2)/alpha**4
        assert np.isclose(-curvature_base,2+velocity**2/alpha**4)
    rotation = []
    ell2 = 2.
    for initial in (1.,1.01,1.15):
        def radial(t,y):
            a,v = y
            return v, ell2/a**3-2*a**3
        sol = solve_ivp(radial,(0.,15.),(initial,0.),t_eval=np.linspace(0.,15.,2001),
                        method="DOP853",rtol=2e-13,atol=2e-15)
        assert sol.success
        a,v = sol.y
        conserved = .5*(v*v+ell2/a**2+a**4)
        assert np.ptp(conserved)<3e-10
        k = ell2/a**6-2-v*v/a**4
        rotation.append(dict(initial_radius=initial,min_angular_pressure=float((-k).min()),
                             max_angular_pressure=float((-k).max()),
                             max_energy_drift=float(np.ptp(conserved))))
    assert rotation[0]["max_angular_pressure"]==0
    assert max(abs(rotation[1][x]) for x in ("min_angular_pressure","max_angular_pressure"))<1
    assert max(abs(rotation[2][x]) for x in ("min_angular_pressure","max_angular_pressure"))>1
    return dict(adjoint_spectra=spectra,heat_traces=rows,rotating_solutions=rotation)


def rotating_receiver():
    # Canonically normalized spin-one transverse modes of a circular receiver.
    # A smooth enveloped tide avoids the broad edge spectrum of a rectangular pulse.
    alpha = 1.
    omega = np.sqrt(2)*alpha
    duration = 12*np.pi/omega
    rows = []
    for ratio, strength in ((1.,.002),(1.,.02),(1.18,.002),(1.18,.02)):
        def tide(t):
            return strength*omega**2 * np.sin(np.pi*t/duration)**2 * np.cos(2*ratio*omega*t)
        def integral(component):
            return quad(lambda t: tide(t)*component(2*omega*t),0,duration,
                        epsabs=5e-14,limit=180)[0]
        response = integral(np.cos)+1j*integral(np.sin)
        perturbative = 3*abs(response)**2/(4*omega**2)
        occupations = []
        for sign in (-1,1):
            def linear_flow(t,y):
                m = y.reshape(2,2)
                return (np.array([[0.,1.],[-omega**2+sign*tide(t),0.]]) @ m).reshape(-1)
            sol = solve_ivp(linear_flow,(0.,duration),np.eye(2).reshape(-1),method="DOP853",
                            rtol=1e-12,atol=2e-14)
            assert sol.success
            m = sol.y[:,-1].reshape(2,2)
            assert abs(np.linalg.det(m)-1)<4e-12
            n = ((m[0,0]-m[1,1])**2+(omega*m[0,1]+m[1,0]/omega)**2)/4
            occupations.append(float(n))
        prob = -np.expm1(-1.5*sum(np.log1p(occupations)))
        if strength < .01:
            assert abs(prob/perturbative-1)<3e-4
        rows.append(dict(frequency_ratio=ratio,peak_tide_in_omega_squared=strength,
                         pulse_in_receiver_cycles=6.,first_order_probability=perturbative,
                         exact_quadratic_probability=float(prob)))
    assert rows[2]["exact_quadratic_probability"] < rows[0]["exact_quadratic_probability"]*.005
    return rows


def figure(report,path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (a,b) = plt.subplots(1,2,figsize=(8.4,3.0),layout="constrained")
    v = np.linspace(0,1.5,180)
    a.plot(v,np.exp(-pi*v*v),label="Ordinary probe")
    a.axhline(1,color="darkorange",ls="--",label="Graded receipt, occupied")
    a.set(xlabel="Normal gap / square root of sweep rate",ylabel="Transition probability",
          ylim=(-.035,1.08))
    a.legend(frameon=False,fontsize=8)
    for label, legend in (("Page_content","Page particle content"),("relativistic_SM","Hot Standard Model")):
        rows = [r for r in report["string"]["finite_release"] if r["content"]==label]
        b.semilogy([1-r["final_mass_fraction"] for r in rows],
                   [r["exact_heralded_rate"] for r in rows],"o-",label=legend)
    b.set(xlabel="Fraction of mass radiated",ylabel="Heralded recovery from radiation")
    b.legend(frameon=False,fontsize=8)
    fig.savefig(path)
    plt.close(fig)

    fig, (a,b) = plt.subplots(1,2,figsize=(8.4,3.0),layout="constrained")
    radius, speed = np.meshgrid(np.linspace(.8,1.24,280),np.linspace(-.85,.85,240))
    pressure = 2+speed**2/radius**4-2/radius**6
    a.contourf(radius,speed,np.abs(pressure),levels=[-1,1],colors=["#c4dfed"])
    a.contour(radius,speed,pressure,levels=[-1,1],colors=["#296181"],linewidths=1)
    a.plot(1,0,"ko",ms=4)
    a.set(xlabel="Radius parameter",ylabel="Radial velocity")
    duration = 12*pi  # time measured in inverse receiver frequency
    ratios = np.linspace(.8,1.2,401)
    def flat(freq):
        return duration*np.exp(1j*freq*duration/2)*np.sinc(freq*duration/(2*pi))
    def pulse(freq):
        return flat(freq)/2-(flat(freq+2*pi/duration)+flat(freq-2*pi/duration))/4
    amplitude = .001*(pulse(2*(1-ratios))+pulse(2*(1+ratios)))
    b.plot(ratios,3*abs(amplitude)**2/4*1e4,color="#296181")
    exact = [row for row in report["gravitational_preparation"]
             if row["peak_tide_in_omega_squared"]==.002]
    b.scatter([r["frequency_ratio"] for r in exact],
              [1e4*r["exact_quadratic_probability"] for r in exact],s=24,color="#b34d22")
    b.set(xlabel="Source radius / receiver radius",ylabel="Pair probability (in units of 0.0001)")
    fig.savefig(path.with_name("layer_matrix_receiver.pdf"))
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    report=dict(localizer=localizers(), crossing=dynamical_crossing(),
                protected=logical_outcomes(),energy_matched=energy_matched_receipts(),
                string=compactified_emission(),geometry=four_dimensional_probe(),
                gravitational_preparation=rotating_receiver())
    (ROOT/"verification/layer-matrix-parent-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        figure(report,args.figure)
    print("Matrix spectral flow, material output, retention and compactified radiation checked.")
