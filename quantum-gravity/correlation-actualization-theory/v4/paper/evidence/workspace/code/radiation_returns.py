"""Finite optical receipts, dipole re-emission and Schwarzschild pair spectra.

Run from the repository or the extracted workspace with Python, NumPy and SciPy.
The greybody solver is the one distributed with the earlier part of this paper.
"""
import argparse
import json
from math import comb, exp, expm1, factorial, log, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import beta, gammainc

from fusion_surface_memory import greybody

ROOT = Path(__file__).resolve().parents[1]


def dark_probability(z):
    # Time is measured in units of the incident amplitude lifetime.
    # Lower incomplete gamma avoids subtracting nearly equal numbers at z=0.
    return sum(c * factorial(n) * gammainc(n + 1, 2*z) / 2**n
               for n, c in ((2, 4), (3, -4), (4, 1)))


def receiver():
    eye = np.eye(2)
    swap = np.fliplr(eye)
    sign = np.diag([-1, 1])
    error = 0.
    for detuning in [-5, -1, -.14, 0, .35, 1, 4]:
        r = (1j*detuning-1)/(1j*detuning+1)
        left, right = np.diag([r, 1]), np.diag([1, r])
        for theta in [0, .32, 1.47, pi]:
            c, d = np.cos(theta/2), -1j*np.sin(theta/2)
            u = c*eye + d*swap   # Common phase removed.
            arm0, arm1 = right@u@left, left@u@right
            dark, bright = (arm0-arm1)/2, (arm0+arm1)/2
            det = d*(1-r*r)/2 * swap@sign
            error = max(error, np.linalg.norm(dark-det),
                        np.linalg.norm(bright-(r*c*eye+d*(1+r*r)/2*swap)),
                        np.linalg.norm(dark.conj().T@dark+bright.conj().T@bright-eye))
    gamma = 6.265e8
    clocks = {"grain": .4074e-12, "human": 1.534e-9, "stellar_window": 3.0602e-6}
    windows = {}
    for label, seconds in clocks.items():
        z = gamma*seconds/2
        p = dark_probability(z)
        numerical = quad(lambda t: 2*exp(-2*t)*t*t*(2-t)**2, 0, min(z, 50),
                         epsabs=1e-25)[0]
        assert abs(numerical-p) < 1e-12*max(p, 1e-14)
        windows[label] = dict(seconds=seconds, aT=z, probability=p,
                              independent_trials_for_99pct=int(np.ceil(log(.01)/np.log1p(-p))))
    assert error < 1e-12
    return dict(max_matrix_error=error, windows=windows, infinite_time=dark_probability(800))


def sorted_charge():
    # A singlet and a direction supplied by the retarded stellar field.
    # Each readout is followed by an exchange only for the reversed ordering.
    sigma = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]])
    eye = np.eye(2)
    swap = np.eye(4)[[0,2,1,3]]
    singlet = np.array([0.,1,-1,0])/sqrt(2)
    err = 0.
    def states(n):
        nonlocal err
        plus = (eye+np.einsum("i,ijk->jk", n, sigma))/2
        minus = eye-plus
        k0 = np.kron(minus, plus)
        k1 = swap@np.kron(plus, minus)
        branches = k0@singlet, k1@singlet
        rho = sum(np.outer(v,v.conj()) for v in branches)
        err = max(err, np.linalg.norm(branches[0]+branches[1]),
                  abs(np.vdot(branches[0],branches[0])-.5),
                  np.linalg.norm(rho-np.kron(minus,plus)))
        # Obtain Berry links from the two material outputs after selection.
        one = rho.reshape(2,2,2,2)
        return [np.linalg.eigh(one.trace(axis1=a,axis2=b))[1][:,-1]
                for a,b in [(1,3),(0,2)]]
    def orient_triangle(u,v,w):
        if np.dot(u,np.cross(v,w)) < 0:
            return u,w,v
        return u,v,w
    xyz = np.eye(3)
    triangles = [orient_triangle(i*xyz[0], j*xyz[1], k*xyz[2])
                 for i in (-1,1) for j in (-1,1) for k in (-1,1)]
    fluxes = []
    for order in range(3):
        flux = np.zeros(2)
        for u,v,w in triangles:
            for index, (a,b,c) in enumerate(zip(states(u),states(v),states(w))):
                flux[index] += np.angle(np.vdot(a,b)*np.vdot(b,c)*np.vdot(c,a))
        fluxes.append((flux/(2*pi)).tolist())
        if order < 2:
            sub = []
            for u,v,w in triangles:
                ab,bc,ca = [(a+b)/np.linalg.norm(a+b) for a,b in [(u,v),(v,w),(w,u)]]
                sub.extend([(u,ab,ca),(v,bc,ab),(w,ca,bc),(ab,bc,ca)])
            triangles = sub
    assert np.allclose(fluxes, [[-1,1]]*3) and err<2e-15
    hbar_ev_s = 6.582119569e-16
    window = 63.57e-6
    min_exchange = pi*hbar_ev_s/window
    return dict(max_state_error=err, boundary_companion_chern=fluxes,
                available_seconds=window, min_constant_exchange_eV=min_exchange,
                illustrative_swap_seconds_at_0p44meV=pi*hbar_ev_s/(.44e-3),
                thermal_failure={str(b):2*exp(-b)/(1+3*exp(-b)) for b in [1,5,10]})


def quantum_reference():
    from scipy.linalg import expm
    sx = np.array([[0.,1],[1,0]])
    sy = np.array([[0.,-1j],[1j,0]])
    sz = np.diag([1.,-1])
    sigma = [sx,sy,sz]
    singlet = np.array([0.,1.,-1.,0.])/sqrt(2)
    swap_sites = np.eye(4)[[0,2,1,3]]
    rows = []
    for n in [1,2,3,4,8]:
        j = n/2
        # Descending magnetic quantum number. hbar=1 in the spin algebra.
        raising = np.diag([sqrt(k*(n-k+1)) for k in range(1,n+1)], 1)
        spin = [(raising+raising.T)/2,(raising-raising.T)/(2*1j),
                np.diag(np.arange(j,-j-1,-1))]
        ident = np.eye(n+1)
        dot = sum(np.kron(a,b) for a,b in zip(spin,sigma))
        low_ref = (j*np.eye(2*(n+1))-dot)/(n+1)
        low = np.kron(low_ref,np.eye(2))
        high = np.eye(4*(n+1))-low
        alift = np.kron(ident, singlet[:,None])
        ps = alift@alift.conj().T
        q = j/(2*j+1)
        c = (low@ps-ps@low)/sqrt(q*(1-q))
        correct = expm((pi/2)*c)
        vl = low@alift/sqrt(q)
        vh = high@alift/sqrt(1-q)
        comm_error = 0.
        for a,b in zip(spin,sigma):
            total = np.kron(a,np.eye(4))+np.kron(ident,(np.kron(b,np.eye(2))+np.kron(np.eye(2),b))/2)
            comm_error = max(comm_error,np.linalg.norm(c@total-total@c))
        failread = np.kron(ident,np.kron(np.diag([1.,0]),np.eye(2)))
        simple = [low@alift[:,0], np.kron(ident,swap_sites)@high@alift[:,0]]
        wrong = sum(np.vdot(u,failread@u).real for u in simple)
        # Use spin lowering in R+site 1 to construct the actual outgoing l basis.
        l = j-.5
        refminus = spin[0]-1j*spin[1]
        lower = np.kron(refminus,np.eye(2))+np.kron(ident,(sx-1j*sy)/2)
        top = vl[:,0].reshape(2*(n+1),2)[:,0]
        basis = [top]
        for k in range(n-1):
            basis.append(lower@basis[-1]/sqrt((2*l-k)*(k+1)))
        outputs = np.kron(np.array(basis).conj(),np.eye(2))@vl
        expected = np.zeros_like(outputs)
        for k in range(n+1):
            if k<n:
                expected[2*k,k]=sqrt((n-k)/n)
            if k>0:
                expected[2*(k-1)+1,k]=sqrt(k/n)
        mismatch=max(comm_error,np.linalg.norm(correct@vh-vl),np.linalg.norm(vl.conj().T@vl-ident),
                     np.linalg.norm(outputs-expected),abs(wrong-(4*j+1)/(2*(2*j+1)**2)))
        assert mismatch<2e-13
        rows.append(dict(two_j=n,low_born=q,wrong_individual_spin=wrong,
                         norm_and_covariance_error=mismatch))
    # Iterate the derived Clebsch--Gordan map; compare to independent binary weights.
    code = np.ones((1,1))
    for n in range(1,10):
        out = np.zeros((2**n,n+1))
        for k in range(n+1):
            if k<n:
                out[::2,k]=sqrt((n-k)/n)*code[:,k]
            if k>0:
                out[1::2,k]=sqrt(k/n)*code[:,k-1]
        expected = np.zeros_like(out)
        for word in range(2**n):
            k=word.bit_count()
            expected[word,k]=1/sqrt(comb(n,k))
        assert np.linalg.norm(out-expected)<4e-14
        code=out
    return dict(spin_tests=rows, complete_symmetric_encoder_bits=9,
                last_isometry_error=np.linalg.norm(code.T@code-np.eye(10)))


def nonround_cut():
    axes = np.array([1.3,.8,1.7])
    largest = 0.
    low, high = np.inf, 0.
    for theta in np.linspace(.18, pi-.18, 17):
        s, c = np.sin(theta), np.cos(theta)
        for phi in np.arange(25)*2*pi/25:
            u, v = np.cos(phi), np.sin(phi)
            xt = axes*np.array([c*u,c*v,-s])
            xp = axes*np.array([-s*v,s*u,0])
            xtt = -axes*np.array([s*u,s*v,c])
            xtp = axes*np.array([-c*v,c*u,0])
            xpp = axes*np.array([-s*u,-s*v,0])
            area_vec = np.cross(xt,xp)
            area = np.linalg.norm(area_vec)
            normal = area_vec/area
            tangent = np.eye(3)-np.outer(normal,normal)
            nt = tangent@(np.cross(xtt,xp)+np.cross(xt,xtp))/area
            np_ = tangent@(np.cross(xtp,xp)+np.cross(xt,xpp))/area
            solid = normal@np.cross(nt,np_)
            intrinsic = ((normal@xtt)*(normal@xpp)-(normal@xtp)**2)/area
            largest = max(largest, abs(solid-intrinsic))
            low, high = min(low, intrinsic/area), max(high, intrinsic/area)
    assert largest<5e-14 and high>8*low
    return dict(samples=425, axes=axes.tolist(), max_curvature_density_error=largest,
                gaussian_curvature_range=[low,high])


def scattering():
    cosines, weights = np.polynomial.legendre.leggauss(8)
    nodes = []
    for u, w in zip(cosines, weights):
        for phi in np.arange(12)*pi/6:
            n = np.array([np.sqrt(1-u*u)*np.cos(phi), np.sqrt(1-u*u)*np.sin(phi), u])
            nodes.append((3*w/48, np.eye(3)-np.outer(n, n)))
    # 3/(8 pi) times w times 2 pi/12.
    ep = np.array([1, 1j, 0])/sqrt(2)
    em = ep.conj()
    initial = np.outer(ep, em.conj())
    channel = lambda x: sum(w*p@x@p for w, p in nodes)
    exact = lambda x: (6*x+x.T+np.trace(x)*np.eye(3))/10
    err = max(np.linalg.norm(channel(x)-exact(x)) for x in
              np.eye(9).reshape(9, 3, 3))
    x = initial
    trial = []
    for n in range(1, 6):
        # Orthogonal final photon direction is readable. Its block trace norms add.
        v = sum(w*np.linalg.svd(p@x@p, compute_uv=False).sum() for w, p in nodes)
        assert abs(v-.7**(n-1)) < 1e-12
        trial.append(dict(scatterings=n, visibility=v, entanglement_fidelity=(1+v)/2))
        x = channel(x)
    assert err < 2e-14
    soft = {}
    for eta in [2, 4, 6]:
        vals = {}
        for x in [.1, .01, .001]:
            t = 4/9*(x/(4*pi))**4
            p = -expm1(-1e-5*x**eta)
            vals[str(x)] = t/(t+.3*(1-t)*p)
        soft[str(eta)] = vals
    norm = quad(lambda z: z**5*exp(-z*z), 0, np.inf)[0]
    assert abs(norm-1) < 2e-13
    return dict(angular_channel_max_error=err, recoverable=trial,
                example_soft_visibilities=soft, gaussian_quadrupole_integral=norm)


def widths(n, nu):
    # The area gap is log(2). Couplings and the Planck mass are unity ONLY
    # in this scaling test. e^{-S_n} times daughter degeneracy is 2^{-j}.
    gap = log(2)
    mass = sqrt(n*gap/(4*pi))
    rate = power = 0.
    for j in range(1, min(n, 110)):
        q = sqrt(1-j/n)
        delta = (j/n)/(1+q)
        def weight(z):
            return ((1-z)*((1+q)**2-delta**2*z))**2.5
        common = (n*gap)**nu*mass**9*2.**(-j)*delta**7/(480*pi**3)
        rate += common*quad(weight, 0, 1, epsabs=1e-10)[0]
        power += common*mass/2*quad(lambda z: weight(z)*(j/n+delta**2*z),
                                    0, 1, epsabs=1e-10)[0]
    return mass, rate, power


def pair_spectrum():
    x = np.array([4., 5., 6.])
    raw = {s: np.array([greybody(x/(4*pi), ell, s, 1) for ell in range(1, 9)])
           for s in [1, 2, 4]}
    limits = []
    for scale in [1, 2]:
        trans = raw[2*scale]+(raw[2*scale]-raw[scale])/15
        for cutoff in [1, 6, 8]:
            weights = 2*(2*np.arange(1, cutoff+1)+1)
            h = (weights@trans[:cutoff])/(np.expm1(x)*x**3)
            difference = h[0]-2*h[1]+h[2]
            limits.append(dict(scale=scale, ellmax=cutoff, reduced=h.tolist(),
                               second_difference=difference,
                               relative_error_floor=-difference/(h[0]+2*h[1]+h[2])))
    assert all(r["second_difference"] < 0 for r in limits)
    assert abs(limits[-1]["second_difference"]-limits[2]["second_difference"]) < 2e-10
    mass_law = {}
    for nu in [0, 1, 2]:
        rows = [widths(n, nu) for n in [100, 500, 2000, 8000]]
        mass_law[str(nu)] = dict(rows=rows, logarithmic_slopes=[
            log(rows[-1][k]/rows[-2][k])/log(rows[-1][0]/rows[-2][0]) for k in [1, 2]])
        assert abs(mass_law[str(nu)]["logarithmic_slopes"][1]-(2*nu-6)) < .02
    # Invert the positive kernel independently by summing the fourth derivative
    # of e^{-j x}/x^3. Reconstruction uses no black-hole transmission fit.
    def w(s):
        return sum(exp(-j*s)*sum(comb(4,k)*j**(4-k)*factorial(k+2)/(2*s**(k+3))
                                 for k in range(5)) for j in range(1, max(2, int(52/s)+2)))/6
    inv = {}
    for z in [.2, 1., 4.]:
        est = quad(lambda s: (s-z)**3*w(s), z, z+55, epsabs=1e-12)[0]
        target = 1/(z**3*expm1(z))
        inv[str(z)] = est/target
    assert max(abs(v-1) for v in inv.values()) < 2e-11
    ir = [140*beta(8+k,4)/(4+k) for k in (0,1)]
    assert np.allclose(ir, [7/264, 7/495])
    return dict(schwarzschild=limits, area_ladder=mass_law, inversion_ratios=inv,
                soft_moment_coefficients=ir)


def figure(path, report):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, (a, b) = plt.subplots(1, 2, figsize=(8, 3.15), layout="constrained")
    z = np.geomspace(.04, 12, 260)
    a.semilogx(z, dark_probability(z), color="#225b70")
    a.set(xlabel=r"Time in amplitude lifetimes, $aT$", ylabel="Probability of a dark-port photon")
    a.axhline(.5, lw=.8, ls=":", color="0.45")
    row = report["spectra"]["schwarzschild"][-1]
    h = np.array(row["reduced"])*1e5
    b.plot([4,6], h[[0,2]], "--", color="0.5", label="Chord between 4 and 6")
    b.plot([4,5,6], h, "o", color="#923e29", label="Schwarzschild photons")
    b.set(xlabel=r"Photon energy, $\omega/T_H$", ylabel=r"Reduced number spectrum, $10^5 F(x)/x^3$")
    b.set_xticks([4,5,6])
    b.legend(fontsize=8, frameon=False)
    fig.savefig(path)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path)
    args = parser.parse_args()
    report = dict(receipt=receiver(), charge=sorted_charge(), quantum_reference=quantum_reference(), nonround=nonround_cut(), reabsorption=scattering(), spectra=pair_spectrum())
    (ROOT/"verification/radiation-returns-results.json").write_text(
        json.dumps(report, indent=2, allow_nan=False)+"\n", encoding="utf8")
    if args.figure:
        figure(args.figure, report)
    print("Finite-time receipts, repeated dipole scattering and the pair spectrum passed.")
