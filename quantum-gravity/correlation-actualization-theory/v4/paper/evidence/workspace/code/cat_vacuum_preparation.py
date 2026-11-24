"""Gravitational preparation of a CAT receiving matrix from its fast-mode vacuum.

Matrix energy units have hbar=1. The distance in matrix coordinates is an
energy; the gauge scale ell=(g_1^2)^(1/3) is set to one in tabulated examples.
"""
import argparse
import json
from fractions import Fraction
from math import exp, factorial, lgamma, log, pi, sqrt
from pathlib import Path

import numpy as np
from scipy import linalg, special
from scipy.integrate import quad, solve_ivp
from scipy.stats import qmc

ROOT = Path(__file__).resolve().parents[1]
PAULI = (
    np.array([[0., 1.], [1., 0.]]),
    np.array([[0., -1j], [1j, 0.]]),
    np.diag([1., -1.]),
)


def index_on_axis(columns, xi):
    gram = np.swapaxes(columns, -2, -1) @ columns
    trace = np.trace(gram, axis1=-2, axis2=-1)
    determinant = gram[..., 0, 0]*gram[..., 1, 1] - gram[..., 0, 1]**2
    return (xi-trace)**2 < 4*determinant


def collective_motion():
    """Evolve the ordinary BFSS equations before applying any charge readout."""
    leaves = 8
    n = leaves+1
    offsets = np.linspace(.7,2.45,leaves)
    Z = np.diag(np.r_[-offsets,1.])
    Wdot = np.zeros((n,n),complex)
    Wdot[:leaves,-1] = 10*np.sqrt(offsets/leaves)*np.exp(2j*pi*np.arange(leaves)/leaves)
    def xy(w):
        return (w+w.conj().T)/2,(w.conj().T-w)/(2j)
    zero = np.zeros_like(Wdot)
    positions = np.array([zero,zero,Z])
    velocities = np.array([*xy(Wdot),zero])
    def comm(a,b): return a@b-b@a
    tidal_start=1.16
    def tide(t): return 2/(9*(tidal_start-t)**2)
    def motion(t,state,tidal):
        coords,speeds=state.reshape(2,3,n,n)
        force=np.zeros_like(coords)
        for i in range(3):
            for k in range(i):
                bracket=comm(coords[k],coords[i])
                force[i]-=comm(coords[k],bracket)
                force[k]+=comm(coords[i],bracket)
        if tidal:
            force-=tide(t)*coords
        return np.array([speeds,force]).ravel()
    def conserved(x,v):
        kinetic=sum(np.linalg.norm(a)**2 for a in v)/2
        potential=sum(np.linalg.norm(comm(x[i],x[k]))**2 for i in range(3) for k in range(i))/2
        gauss=np.linalg.norm(sum(comm(a,b) for a,b in zip(x,v)))
        return kinetic+potential,gauss
    driven=solve_ivp(motion,(0.,.18),np.array([positions,velocities]).ravel(),args=(True,),dense_output=True,
                     method="DOP853",rtol=3e-12,atol=1e-13)
    ordinary=solve_ivp(motion,(0.,.18),np.array([positions,velocities]).ravel(),args=(False,),dense_output=True,
                       method="DOP853",rtol=3e-12,atol=1e-13)
    assert driven.success and ordinary.success
    energy,_=conserved(positions,velocities)
    def geometry(t,out=driven):
        x,v=out.sol(t).reshape(2,3,n,n)
        current,gauss=conserved(x,v)
        if out is driven:
            # Explicit work of the curvature. Compare its integral against
            # the ordinary Hamiltonian plus the tidal potential at the cut.
            def work_rate(s):
                coords=out.sol(s).reshape(2,3,n,n)[0]
                return 2*np.linalg.norm(coords)**2/(9*(tidal_start-s)**3)
            work=quad(work_rate,0.,t)[0]
            initial=energy+tide(0)*np.linalg.norm(positions)**2/2
            assert abs(current+tide(t)*np.linalg.norm(x)**2/2-initial-work)<3e-8
        else:
            assert abs(current-energy)<2e-8
        assert gauss<2e-9
        for i in range(3):
            for j in range(i):
                assert abs(np.trace(x[i]@v[j]-x[j]@v[i]))<2e-9
        # Eigenvectors of the nondegenerate material Z define the pair labels.
        z,U=linalg.eigh(x[2])
        ordered=[U.conj().T@a@U for a in x]
        w=ordered[0]-1j*ordered[1]
        assert z[-2]<0<z[-1] and np.linalg.norm(w[:-1,:-1])+np.linalg.norm(w[-1,:])<1e-9
        weights=abs(w[:-1,-1])**2/(-z[:-1])
        spectrum=linalg.eigvalsh(sum(np.kron(s,a) for s,a in zip(PAULI,x)))
        index=int(sum(np.sign(spectrum))/2)
        ratios=weights/z[-1]
        if min(abs(spectrum))>1e-9:
            assert index==int(sum(ratios)>1)
        return float(sum(ratios)-1),float(max(ratios)),float(min(abs(spectrum))),index
    from scipy.optimize import brentq
    crossing=brentq(lambda t: geometry(t)[0],0.,.15)
    snapshots=[]
    for t in (0.,.08,.12,.15,.16):
        ratio,maximum,gap,index=geometry(t)
        snapshots.append(dict(time=t,collective_ratio=1+ratio,largest_pair_ratio=maximum,gap=gap,index=index))
    assert snapshots[0]["index"]==0 and snapshots[-1]["index"]==1 and snapshots[-1]["largest_pair_ratio"]<1
    # Rational static witness: no individual pair reaches its own threshold.
    assert 4/2<3 and 4/3<3 and 4/2+4/3>3
    vacuum_crossing=brentq(lambda t: geometry(t,ordinary)[0],0.,.15)
    return dict(leaves=leaves,crossing=crossing,tideless_crossing=vacuum_crossing,
                birth_remaining_over_horizon=tidal_start,snapshots=snapshots,
                time_to_horizon_us_10_solar=(.16-crossing)*65.6732126352169)


def geometry_checks():
    rng = np.random.default_rng(147)
    maximum_gap_error = 0.
    # Start and end points of each trial avoid the zero set.
    for _ in range(64):
        columns = rng.normal(size=(8, 2))
        b, c = linalg.svdvals(columns)
        a = 12.
        point = rng.uniform(-2, 2, 3) + [0., 0., rng.uniform(7, 16)]
        pencil = sum(np.kron(s, q*s-y*np.eye(2)) for s, q, y in zip(PAULI, (b,c,a), point))
        spectrum = linalg.eigvalsh(pencil)
        index = int(sum(np.sign(spectrum))/2)
        distances = [np.linalg.norm(point-[0., 0., t]) for t in (a,-a)]
        if np.prod(distances) > (b+c)**2:
            assert index == 0
        x = a*a-point[2]**2
        axial = sum(np.kron(s, q*s-y*np.eye(2))
                    for s, q, y in zip(PAULI, (b,c,a), (0.,0.,point[2])))
        assert (sum(np.sign(linalg.eigvalsh(axial))) == 2) == index_on_axis(columns,x)
        # One extra Clifford generator anticommutes with the ordinary pencil.
        perp = 1.7
        extended = np.kron(PAULI[2], pencil) + perp*np.kron(PAULI[0], np.eye(4))
        target = np.sort(np.repeat(spectrum**2+perp**2, 2))
        observed = np.sort(linalg.eigvalsh(extended)**2)
        maximum_gap_error = max(maximum_gap_error, np.max(abs(observed-target)))
    assert maximum_gap_error < 1e-10
    return dict(trials=64, extra_direction_squared_gap_verified=True)


def log_gamma_tail(shape, x):
    powers = np.arange(shape, dtype=float)
    return float(-x + special.logsumexp(powers*log(x)-special.gammaln(1+powers)))


def vacuum_region(d, xi, absorbed=False):
    """Stable one-dimensional radial integral, including the one-quantum state."""
    lower = xi/2
    def density_offset(offset):
        s = lower+offset
        v = abs(1-xi/s)
        v = min(1.,v)
        # Integrate the angular condition 2bc > |s-xi| at fixed radial s.
        first = -np.expm1((d-1)*log(v)) if v else 1.
        if absorbed:
            last = -np.expm1((d+1)*log(v)) if v else 1.
            first = (s*s/(2*(d-1)*(d+2))
                     *((1-1/d)*first - (d-1)/(2*(d+1))*last))
        return exp((d-1)*log(s)-offset/2-d*log(2)-lgamma(d))*first
    value = quad(density_offset,0,lower,epsabs=1e-12,epsrel=2e-11)[0]
    value += quad(density_offset,lower,np.inf,epsabs=1e-12,epsrel=2e-11)[0]
    return log(value)-lower/2


def hankel_gain(p, tidal, u, ru):
    order = sqrt(.25-tidal)/(1+p)
    z = ru*u**(1+p)/(1+p)
    return pi*z/2*abs(special.hankel1(order,z))**2


def collapse_modes():
    # u is in terminal-clock units and ru = R_h*u_h. Integrate the original
    # oscillator with its incoming Hankel boundary data; evaluate at the cut.
    out = []
    for name,p,q in (("dust_external",2/3,2/9),("dust_internal",2/3,0.),
                      ("Kasner_stretch",3/7,-18/49),("Kasner_other",3/7,6/49)):
        for ru in (.05,1.,5.):
            nu = sqrt(.25-q)/(1+p)
            def f_and_derivative(u):
                z = ru*u**(1+p)/(1+p)
                h = special.hankel1(nu,z)
                return np.array([sqrt(u)*h, h/(2*sqrt(u))+sqrt(u)*special.h1vp(nu,z)*ru*u**p])
            def motion(u,state):
                return (state[1], -(ru**2*u**(2*p)+q/u**2)*state[0])
            last = solve_ivp(motion,(5.,1.),f_and_derivative(5.),method='DOP853',
                             rtol=2e-11,atol=5e-13).y[:,-1]
            np.testing.assert_allclose(last,f_and_derivative(1.),rtol=2e-10,atol=2e-10)
            gain = hankel_gain(p,q,1.,ru)
            assert (gain>1.) == (nu>.5)
            out.append(dict(mode=name, gap_times_clock=ru, order=nu, position_variance_ratio=float(gain)))
    k = 36.
    return dict(transfers=out, largest_single_Kasner_power=(sqrt(5)-2)/2)


def finite_pump(n, scaled_time):
    """Return p_j with y=gamma sqrt(N) T. All emitted quanta are retained."""
    j = np.arange(n, dtype=float)
    links = (j+1)*np.sqrt((n-j)/n)
    eig, eigenvectors = linalg.eigh_tridiagonal(np.zeros(n+1),links)
    amplitudes = eigenvectors @ (eigenvectors[0]*np.exp(-1j*scaled_time*eig))
    probs = abs(amplitudes)**2
    np.testing.assert_allclose(probs.sum(),1.,atol=1e-12)
    return probs


def active_exact(j, x):
    low = special.gammainc(j+1,x)
    return 2*low*special.gammaincc(j+1,x)


def draw_geometry(uniforms, j, x, d):
    # In the two pumped rows the two opposite colour charges have independent
    # radial gamma variables t_+ and t_-. The other d-2 rows remain in vacuum.
    t = special.gammaincinv(np.asarray(j)[...,None]+1,uniforms[:, :2])
    b2 = (np.sqrt(t[:,0])+np.sqrt(t[:,1]))**2
    c2 = (np.sqrt(t[:,0])-np.sqrt(t[:,1]))**2
    if d == 2:
        return (np.minimum(t[:,0],t[:,1])<x) & (x<np.maximum(t[:,0],t[:,1]))
    if d < 4:
        raise ValueError("The Bartlett implementation requires at least two inactive rows.")
    w11 = 2*special.gammaincinv((d-2)/2,uniforms[:,2])
    z = special.ndtri(uniforms[:,3])
    extra = 2*special.gammaincinv((d-3)/2,uniforms[:,4])
    w22 = z*z+extra
    tr = b2+c2+w11+w22
    det = (b2+w11)*(c2+w22)-w11*z*z
    return (4*x-tr)**2 < 4*det


def geometry_trials():
    # Scramblings assess numerical integration error, independently of the
    # Born distribution. The physical ensemble is fixed by the oscillator state.
    cases = ((0,2.),(1,2.),(5,6.),(19,20.),(89,90.),(719,720.),(19599,19600.))
    points = []
    for seed in (40,82,119,147):
        points.append(qmc.Sobol(6,scramble=True,seed=seed).random_base2(15))
    rows = []
    for j,x in cases:
        estimates = [draw_geometry(u,j,x,8).mean() for u in points]
        m2 = np.mean([draw_geometry(u,j,x,2).mean() for u in points])
        exact2 = active_exact(j,x)
        assert abs(m2-exact2)<.0025
        value = float(np.mean(estimates))
        if j<2:
            np.testing.assert_allclose(value,exp(vacuum_region(8,4*x,absorbed=bool(j))),atol=.002)
        rows.append(dict(absorbed=j, target=x, two_rows_exact=float(exact2),
                         eight_rows=value,replicate_range=[min(estimates),max(estimates)]))
    def limit(d):
        return 1-quad(lambda th:(np.cos(th)/(2+np.cos(th)))**((d-2)/2),0,pi/2)[0]/pi
    assert abs(limit(2)-.5)<1e-14
    assert abs(rows[-1]["eight_rows"]-limit(8))<.004
    # Direct independent sampling after one circularly polarized absorption.
    rng=np.random.default_rng(14711)
    z=rng.normal(size=(131072,8,2))
    circular=z[:,0,:]+1j*z[:,1,:]
    weight=abs(np.sum(circular**2,axis=1))**2/16
    assert abs(weight.mean()-1)<.015
    np.testing.assert_allclose(np.mean(weight*index_on_axis(z,8.)),
                               exp(vacuum_region(8,8.,True)),atol=.015)
    return points,dict(fixed_count=rows, asymptotic_eight_rows=limit(8),
                       asymptotic_two_rows=limit(2),scramblings=4,samples_per_scrambling=32768)


def mesh_counts():
    count=19
    shape=count+1
    rows=[]
    u=qmc.Sobol(2,scramble=True,seed=14712).random_base2(17)
    t=special.gammaincinv(shape,u)
    for m in (1,4,9,99):
        edges=special.gammaincinv(shape,np.arange(1,m+1)/(m+1))
        bins=np.searchsorted(edges,t)
        empirical=np.mean(bins[:,0]!=bins[:,1])
        optimum=m/(m+1)
        assert abs(empirical-optimum)<.001
        rows.append(dict(probes=m,analytic_best=optimum,empirical=empirical))
    return rows


def pump_reports(points):
    output = []
    for n,time,x in ((1,pi/2,2.),(45,1.5,20.),(90,2.3,90.),(180,2.8,90.),(450,3.,90.)):
        p=finite_pump(n,time)
        if n==1:
            np.testing.assert_allclose(p,[0.,1.],atol=1e-14)
        if n<=90:
            j=np.arange(n)
            link=(j+1)*np.sqrt((n-j)/n)
            h=np.diag(link,1)+np.diag(link,-1)
            np.testing.assert_allclose(p,abs(linalg.expm(-1j*time*h)[:,0])**2,atol=1e-12)
        measures=[]
        for u in points:
            cdf=p.cumsum()
            cdf[-1]=1.
            j=np.searchsorted(cdf,u[:,5])
            measures.append(np.mean((j>0)&draw_geometry(u,j,x,8)))
        mean=float(np.dot(p,np.arange(n+1)))
        output.append(dict(incoming=n,scaled_duration=time,target=x,absorption=1-p[0],
                           mean_absorbed=mean,simultaneous_area=float(np.mean(measures)),
                           replicate_range=[min(measures),max(measures)]))
    return output


def rotor_hamiltonian():
    """Ordinary two-rotor quadrupole interaction and the signed input basis."""
    from itertools import combinations, product
    axis=np.array([0.,0.,1.])
    derivative=np.empty((3,3,3,3))
    for indices in product(range(3),repeat=4):
        i,j,k,l=indices
        double_delta=(int(i==j)*int(k==l)+int(i==k)*int(j==l)+int(i==l)*int(j==k))
        mixed=0.
        for a,b in combinations(range(4),2):
            remaining=[r for r in range(4) if r not in (a,b)]
            mixed+=(indices[a]==indices[b])*axis[indices[remaining[0]]]*axis[indices[remaining[1]]]
        derivative[indices]=105*np.prod(axis[list(indices)])-15*mixed+3*double_delta
    coupling=derivative.transpose(0,2,1,3).reshape(9,9)/6
    zero=np.zeros_like(coupling)
    hamiltonian=np.block([[zero,coupling],[coupling,zero]])
    positive=np.array([1.,1j,0.])/sqrt(2)
    basis=np.column_stack((positive,positive.conj()))
    return hamiltonian,basis


def quantum_rotor_effect():
    hamiltonian,basis=rotor_hamiltonian()
    doublet=np.kron(basis,basis)
    rows=[]
    for x in (pi/12,pi/6,pi/2,.35431601):
        transfer=linalg.expm(-1j*x*hamiltonian)[9:,:9]@doublet
        full=(transfer.conj().T@transfer).reshape(2,2,2,2)
        a=np.sin(x)**2
        d=np.sin(6*x)**2/6
        for state in ((1.,0.,0.),(0.,1.,0.),(0.,0.,1.),(.2,-.35,.7),(0.,0.,0.)):
            sx,sy,sz=state
            receiver=(np.eye(2)+sum(v*s for v,s in zip(state,PAULI)))/2
            measured=np.einsum('acbd,dc->ab',full,receiver)
            prediction=((a+d)*np.eye(2)+d*sx*PAULI[0]+d*sy*PAULI[1]+(a-d)*sz*PAULI[2])/2
            np.testing.assert_allclose(measured,prediction,atol=2e-14)
            if state==(1.,0.,0.):
                low,high=linalg.eigvalsh(measured).clip(0,1)
                fidelity=(1+sqrt(low*high)+sqrt((1-low)*(1-high)))/2
                rows.append(dict(area=float(x),parallel=float(a),opposite=float(d),
                                 sign_probability=float(measured[0,0].real),
                                 phase_probabilities=[float(low),float(high)],
                                 recoverable_bell_fidelity=float(fidelity)))
    return rows


def two_unfiltered_exchanges():
    """Use the complete angular manifold at both contacts. The first exchange
    sorts the receiver against a positive witness. Another ordinary forward
    pulse restores the vibrational preparation for every recorded branch.
    """
    from scipy.optimize import brentq
    H,basis=rotor_hamiltonian()
    positive,negative=basis.T
    reference=(positive+negative)/sqrt(2)
    initial=np.r_[np.kron(reference,positive),np.zeros(9)]
    forward=linalg.expm(-1j*pi*H/2)
    backward=linalg.expm(-1j*3*pi*H/2)
    np.testing.assert_allclose(backward@forward,np.eye(18),atol=2e-14)
    splitter=np.diag(np.r_[np.zeros(9),np.ones(9)])
    whole=backward@forward@initial
    marked=[backward@projector@forward@initial for projector in (splitter,np.eye(18)-splitter)]
    for sign,vec in zip((positive,negative),marked):
        np.testing.assert_allclose(vec[:9],np.kron(sign,positive)/sqrt(2),atol=2e-14)
        np.testing.assert_allclose(vec[9:],0.,atol=2e-14)

    common=brentq(lambda x: np.sin(x)**2-np.sin(6*x)**2/6,pi/12,pi/6,xtol=1e-15)
    rows=[]
    for area in (pi/12,common,pi/6,pi/2):
        step=linalg.expm(-1j*area*H)
        a=np.sin(area)**2
        d=np.sin(6*area)**2/6
        row=dict(area=float(area),parallel=float(a),opposite=float(d))
        for name,branches in (("coherent",[whole]),("prior_write",marked)):
            effects=[]
            optimum=0.
            for v in branches:
                # A, receiver, and earlier witness are all retained. The known
                # first vibration is back at its initial endpoint on every h.
                encoded=np.einsum("ai,rw->arwi",basis,v[:9].reshape(3,3)).reshape(9,6)
                for block in (step[9:,:9],step[:9,:9]):
                    amplitude=(block@encoded).reshape(27,2)
                    effects.append(amplitude.conj().T@amplitude)
                    optimum+=linalg.svdvals(amplitude).sum()**2/4
            np.testing.assert_allclose(sum(effects),np.eye(2),atol=2e-14)
            joint=sum(abs(e[0,0]-e[1,1]) for e in effects)/2
            charge=sum(effects[::2])
            np.testing.assert_allclose(charge.diagonal(),(a+d)/2,atol=2e-14)
            if name=="coherent":
                p,q=a/2+d,a/2
                expected=(1+sqrt(p*q)+sqrt((1-p)*(1-q)))/2
                np.testing.assert_allclose(joint,0.,atol=2e-14)
            else:
                expected=(1+sqrt(a*d)+sqrt((1-a)*(1-d)))/2
                np.testing.assert_allclose(joint,abs(a-d),atol=2e-14)
            np.testing.assert_allclose(optimum,expected,atol=2e-14)
            row[name]=dict(joint_sign_contrast=float(joint),optimal_bell_fidelity=float(optimum))
        rows.append(row)
    assert rows[1]["prior_write"]["optimal_bell_fidelity"]>.9999999999
    assert rows[1]["coherent"]["optimal_bell_fidelity"]<.995
    assert rows[-1]["prior_write"]["optimal_bell_fidelity"]<.5000000001
    return rows


def record_discrimination():
    """Two real gravitational receipts. The receiver starts with a coherent
    balanced pair of opposite orientations. h is its earlier record; q measures
    the occupation after the second exchange with A. Keep all ordinary outputs.
    """
    balanced = np.array([[1.,0.],[1.,0.],[0.,1.],[0.,1.]])/sqrt(2)
    # Basis (A+,ref+), (A+,ref-), (A-,ref+), (A-,ref-).
    matched = np.diag([1.,0.,0.,1.])
    ident = np.eye(4)
    result = []
    for area1,area2 in ((0.,pi/2),(pi/6,pi/6),(pi/6,pi/2),(pi/4,pi/2),(pi/2,pi/2)):
        b1, b2 = np.sin([area1,area2])**2
        prior = ((np.sin(area1),0.),(np.cos(area1),1.))
        histories=[]
        for left,right in prior:
            incoming = np.diag([left,right,left,right])@balanced
            # Distinguishable ordinary recoil states are retained isometrically.
            for final in (np.sin(area2)*matched, ident-matched+np.cos(area2)*matched):
                amplitude=final@incoming
                effect=amplitude.conj().T@amplitude
                np.testing.assert_allclose(effect,np.diag(effect.diagonal()),atol=1e-14)
                histories.append(effect)
        outcomes=np.array([e.diagonal() for e in histories]).reshape(2,2,2)
        contrast=.5*abs(outcomes[:,:,0]-outcomes[:,:,1]).sum()
        charge_alone=.5*abs(outcomes.sum(axis=0)[:,0]-outcomes.sum(axis=0)[:,1]).sum()
        fidelity=sum(np.sqrt(e.diagonal()).sum()**2 for e in histories)/4
        np.testing.assert_allclose(outcomes.sum(axis=(0,1)),[1,1],atol=1e-14)
        np.testing.assert_allclose([contrast,charge_alone],[b1*b2,0.],atol=1e-14)
        if area2==pi/2:
            np.testing.assert_allclose(fidelity,(1+abs(np.cos(area1)))/2,atol=1e-14)
        result.append(dict(first_exchange=float(b1),second_exchange=float(b2),
                           charge_guess=(1+float(charge_alone))/2,joint_guess=(1+float(contrast))/2,
                           complete_output_bell_fidelity=float(fidelity)))
    return result


def roundoff_certificate():
    """Exact one-sided rational enclosures for f=1/100, k=36 and x=90.
    Taylor terms alternate for the trigonometric bounds on this interval.
    """
    def exp_lower(x,degree):
        return sum((x**k/factorial(k) for k in range(degree+1)),Fraction(0))
    upper_log=Fraction(717,200)
    upper_area=Fraction(4392,10000)
    upper_tan=Fraction(47,100)
    assert exp_lower(upper_log,24)>36
    assert upper_area**2>Fraction(3,200)*upper_log**2
    assert (upper_area-upper_area**3/6+upper_area**5/120
            < upper_tan*(1-upper_area**2/2+upper_area**4/24-upper_area**6/720))
    # We can evaluate the positive majorant with this larger componentwise
    # pulse area throughout its series. Its resulting expression takes t=.47.
    q=(1+upper_tan**2)/(1-upper_tan**2)/upper_tan**7
    upper=q/exp_lower(90*(1-upper_tan),128)
    assert upper < Fraction(6,10**19)
    return dict(tangent_ceiling=float(upper_tan),joint_upper_below="6e-19")


def energy_deadline():
    # Normal-ordered wave energy for a single circular polarization. All of
    # its allowed density is optimistically assigned to the resonant mode.
    radius_ratio = 36.
    fraction = .01
    area = sqrt(1.5*fraction)*log(radius_ratio)
    mean_limit = np.sinh(area)**2
    tangent = np.tan(area)
    assert 0 < tangent < 1
    bounds = []
    for target in (90.,210.,1680.,19600.):
        # If at most m pairs were made, the radial tail is bounded by the
        # upper tail for m pairs. Markov bounds the larger absorbed counts.
        candidate = np.arange(1, int(target)+1)
        values = mean_limit/(candidate+1)+min(1.,mean_limit)*special.gammaincc(8+2*candidate,target)
        i = int(np.argmin(values))
        log_upper = (-target*(1-tangent)-7*log(tangent)-2*log(np.cos(area))-np.log1p(-tangent**2))
        # Independently sum the radial tails weighted by the positive
        # time-ordered series. Log summation avoids underflow far in the tail.
        if target <= 210:
            j=np.arange(1,401)
            intermediate= -2*log(np.cos(area))+2*j*log(tangent)+np.log(special.gammaincc(8+2*j,target))
            assert special.logsumexp(intermediate) <= log_upper+1e-12
        bounds.append(dict(target=target,count_split=int(candidate[i]),mean_based_upper=float(values[i]),
                           exponential_log10_upper=log_upper/log(10)))
    for n in (1,6,40):
        for duration in (.1,area,1.4):
            actual=np.dot(np.arange(n+1),finite_pump(n,duration))
            assert actual <= np.sinh(duration)**2+1e-12
            if duration<pi/4:
                envelope=(np.tan(duration)**(2*np.arange(n+1)))/np.cos(duration)**2
                assert np.all(finite_pump(n,duration) <= envelope+1e-13)
    return dict(stellar_radius_ratio=radius_ratio,wave_over_dust_ceiling=fraction,
                circular_pulse_area_ceiling=area,absorbed_mean_ceiling=mean_limit,cut_bounds=bounds)


def cut_bounds():
    rows=[]
    for separation,clearance in ((10.,1.),(15.,1.),(30.,2.),(100.,2.)):
        x=separation*clearance*(separation-clearance)
        rows.append(dict(separation=separation,clearance=clearance,target=x,
                         vacuum_log10_bound=log_gamma_tail(8,x)/log(10),
                         one_absorbed_log10_bound=log_gamma_tail(10,x)/log(10)))
    rows[0]["exact_axial_log10"]=vacuum_region(8,4*rows[0]["target"])/log(10)
    rows[0]["axial_after_one_log10"]=vacuum_region(8,4*rows[0]["target"],True)/log(10)
    return rows


def plot(report,path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,(left,right)=plt.subplots(1,2,figsize=(8.6,3.0),layout="constrained")
    chis=np.geomspace(.01,12.,200)
    for p,q,color,label in ((2/3,2/9,"#963f20","dust, ordinary space"),
                             (2/3,0.,"#205c7d","dust, internal directions"),
                             (3/7,-18/49,"#458365","Kasner, stretching axis")):
        left.plot(chis,hankel_gain(p,q,1.,chis),color=color,label=label)
    left.axhline(1,color="#454545",ls=":",lw=.9)
    left.set(xscale="log",xlabel="Mode gap × remaining proper time",
             ylabel="Position variance / bare vacuum variance")
    left.legend(fontsize=7,frameon=False)
    x=np.linspace(0,180,450)
    for count,color in ((1,"#963f20"),(19,"#458365"),(89,"#205c7d")):
        right.plot(x,active_exact(count,x),color=color,label=f"{count} absorbed")
    right.set(xlabel="Inward probe offset in oscillator units, x",
              ylabel="Positive-index probability (two active rows)",ylim=(0,.55))
    right.legend(fontsize=7,frameon=False)
    fig.savefig(path)
    plt.close(fig)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    points,conditional=geometry_trials()
    report=dict(kinematics=geometry_checks(),collective=collective_motion(),record_discrimination=record_discrimination(),
                rotor_effect=quantum_rotor_effect(),two_unfiltered=two_unfiltered_exchanges(),
                rational_certificate=roundoff_certificate(),collapse=collapse_modes(),distant_ports=cut_bounds(),
                charge_geometry=conditional,finite_pumps=pump_reports(points),deadline=energy_deadline(),shared_ports=mesh_counts())
    target=ROOT/"verification/cat-vacuum-preparation-results.json"
    target.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        plot(report,args.figure)
    print("Verified the matrix pencil, collapse modes, helicity transfer, and inclusive receiving probabilities.")
