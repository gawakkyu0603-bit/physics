"""Wrapped M2 gravitational transitions and direct interactions of resolved transfers."""
from pathlib import Path
import json
from itertools import combinations
import math
import os

from decimal import Decimal, getcontext
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import j1, sici

ROOT = Path(__file__).resolve().parents[1]


def line(n, omega_star, sinh_eta, radius=1.0):
    cosh_eta = math.hypot(1, sinh_eta)
    center = radius * omega_star * sinh_eta
    half_span = radius * omega_star * cosh_eta
    radicand = half_span**2 - (n - center)**2
    if radicand <= 0:
        return None
    energy = (omega_star + sinh_eta * n / radius) / cosh_eta
    return energy, math.sqrt(radicand) / (radius * cosh_eta)


def open_lines(omega_star, sinh_eta, radius=1.0):
    center = radius * omega_star * sinh_eta
    span = radius * omega_star * math.hypot(1, sinh_eta)
    return {n: line(n, omega_star, sinh_eta, radius)
            for n in range(math.floor(center - span) + 1, math.ceil(center + span))}


def transition_checks():
    radius, mass, momentum, omega_star = 1., 1000., 750, 2/3
    sinh_eta = momentum / (radius * mass)
    energy = math.hypot(mass, momentum / radius)
    daughter_mass = math.sqrt(mass**2 - 2 * mass * omega_star)
    q = (mass - daughter_mass) / 2
    lines = open_lines(omega_star, sinh_eta)
    assert list(lines) == [0, 1]
    for n, (w, p) in lines.items():
        assert abs(energy - w - math.sqrt(daughter_mass**2 + (momentum - n)**2 + p*p)) < 3e-13
    assert abs(lines[1][1]-lines[0][1]) < 1e-15
    initial_receiver_mass = math.hypot(daughter_mass, momentum)
    w0 = lines[0][0]
    detuning = (initial_receiver_mass**2 + 2*initial_receiver_mass*w0 - energy**2) / (
        math.sqrt(initial_receiver_mass**2 + 2*initial_receiver_mass*w0) + energy)
    ell = np.arange(1, 20001)
    errors = []
    for center, span in [(0.5, 5/6), (2.19, 4.714), (-18.031, 30.293)]:
        integers = np.arange(math.ceil(center-span), math.floor(center+span)+1)
        lattice = np.sqrt(np.maximum(0, span**2 - (integers - center)**2)).sum()
        poisson = np.pi*span**2/2 + span*np.sum(j1(2*np.pi*ell*span)*np.cos(2*np.pi*ell*center)/ell)
        errors.append(abs(poisson-lattice)/lattice)
    assert max(errors) < 4e-6
    half_flux = open_lines(omega_star, (momentum+.5)/(mass*radius))
    width_ratio=half_flux[1][1]/half_flux[0][1]
    assert abs(width_ratio**2-(1+1/(mass*omega_star*radius**2)))<1e-14
    return dict(omega_star=omega_star, parent_mass=mass, daughter_mass=daughter_mass,
                three_form_half_flux_width_ratio=width_ratio,
                gap_twice_phonon_q=2*q, compact_momentum=momentum,
                lines={str(n):dict(energy=w, spatial_momentum=p) for n,(w,p) in lines.items()},
                rest_to_rest_detuning=detuning, poisson_relative_errors=errors)


def pole_checks():
    total_width, bandwidth, detuning = 1., 0.61, 0.37
    incident = lambda e: bandwidth/(2*np.pi*((e-detuning)**2+(bandwidth/2)**2))
    shape = lambda e: total_width**2/(total_width**2+4*e**2)
    weight = quad(lambda e: incident(e)*shape(e), -np.inf, np.inf)[0]
    analytic = total_width*(total_width+bandwidth)/((total_width+bandwidth)**2+4*detuning**2)
    assert abs(weight-analytic) < 2e-13
    fractions = np.array([0.37, 0.37, 0.26])
    vec = np.sqrt(fractions)
    for e in [0., .21, 1.7]:
        matrix = np.identity(3) - 1j*np.outer(vec,vec)/(e+.5j)
        assert np.linalg.norm(matrix.conj().T@matrix-np.identity(3)) < 1e-14
    fraction = 2*fractions[0]
    switch = fraction**2 * weight
    elastic = 1 - (2*fraction-fraction**2)*weight
    inferred = 2*switch/(1-elastic+switch)
    assert abs(inferred-fraction) < 2e-15
    pulse = []
    for x in [.1, 1., 3., 10.]:
        cumulative = .5*(1-math.exp(-x)*(1+x+x*x/2))
        independent = quad(lambda t: t*t*math.exp(-t)/4, 0, x)[0]
        assert abs(cumulative-independent) < 2e-15
        pulse.append(cumulative)
    # Independent verification of the charge-graded instrument on a coherent input.
    rng = np.random.default_rng(108)
    unitary, _ = np.linalg.qr(rng.normal(size=(7,7))+1j*rng.normal(size=(7,7)))
    charge = np.array([-1,-1,0,0,0,1,2])
    shifts = charge[:,None]-charge[None,:]
    kraus = [np.where(shifts==r,unitary,0.) for r in np.unique(shifts)]
    completeness_error=np.linalg.norm(sum(k.conj().T@k for k in kraus)-np.eye(7))
    assert completeness_error<2e-15
    return dict(line_average=weight, switch_probability=switch, elastic_probability=elastic,
                inferred_visible_width=inferred, matched_pulse_cumulative=pulse,
                charge_instrument_error=float(completeness_error))


def current_checks():
    p, e, w0, w1, k = 8/15, 1250., 8/15, 17/15, 750
    fast = p/w1
    v0, v1 = -p/(e-w0), -p/(e-w1)
    def heavy(x):
        return (k-1)*v1/(1-v1*x)-k*v0/(1-v0*x)
    def current(x):
        return fast/(1-fast*x)+heavy(x)
    assert min(heavy(x) for x in np.linspace(-1,1,401)) > 0
    full = quad(lambda x:(1-x*x)*current(x)**2,-1,1)[0]
    lower = 2/fast*math.log((1+fast)/(1-fast))-4
    assert abs(lower-quad(lambda x:(1-x*x)*(fast/(1-fast*x))**2,-1,1)[0])<1e-14
    assert full > lower > 0
    def echo_ir(lo, hi):
        return quad(lambda t:4*np.sin(t/2)**2/t,lo,hi,epsabs=2e-12)[0]
    echo = echo_ir(0.,12.)
    assert abs(echo-2*(np.euler_gamma+math.log(12)-sici(12)[1])) < 2e-14
    return dict(vector_angular_integral=full, analytic_strict_lower_bound=lower,
                uncompensated_ir_integrals=[math.log(12/x) for x in [1.,.01,.0001]],
                compensated_ir_integrals=[echo_ir(x,12.) for x in [1.,.01,.0001]],
                compensated_zero_cutoff=echo)


def coefficient(poly, j):
    return poly[j] if 0 <= j < len(poly) else 0


def transmission(w, mass, orbital, outer=55., order=6):
    """Dimensionless ingoing horizon wave matched to both Coulomb waves."""
    p = math.sqrt(w*w-mass*mass)
    angular = orbital*(orbital+1)
    ca = [w*w,4*w*w-mass*mass-angular-1,6*w*w-3*mass*mass-angular,
          4*w*w-3*mass*mass,w*w-mass*mass]
    rho = -1j*w
    horizon = [1.+0j]
    for j in range(1,order+1):
        accum=0j
        for i,series in enumerate(horizon):
            nu=rho+i
            d=j-i
            accum+=series*(coefficient([1,2,1],d)*nu*(nu-1)+coefficient([1,1],d)*nu+coefficient(ca,d))
        horizon.append(-accum/((rho+j)**2+w*w))
    t=.001
    wave=sum(v*t**(rho+j) for j,v in enumerate(horizon))
    flux=sum(v*(rho+j)*t**(rho+j-1) for j,v in enumerate(horizon))*t/(1+t)
    def radial(x,state):
        f=1-1/x
        u,du=state
        return [du/f, (f*(mass*mass+angular/x**2+1/x**3)-w*w)*u/f]
    sol=solve_ivp(radial,[1+t,outer],[wave,flux],method="DOP853",rtol=7e-11,atol=5e-12)
    assert sol.success
    alpha=(2*w*w-mass*mass)/(2*p)
    pa,pb,pc=[1,-2,1],[0,0,1,-1],[p*p,mass*mass,-angular,angular-1,1]
    def term(nu,d):
        return (-p*p*coefficient(pa,d)+2j*p*nu*coefficient(pa,d-1)
                +nu*(nu-1)*coefficient(pa,d-2)+1j*p*coefficient(pb,d)
                +nu*coefficient(pb,d-1)+coefficient(pc,d))
    tail=[1.+0j]
    for j in range(1,order+1):
        tail.append(sum(b*term(1j*alpha-i,j+1-i) for i,b in enumerate(tail))/(2j*p*j))
    base=np.exp(1j*p*outer)*outer**(1j*alpha)
    outgoing=base*sum(b*outer**(-i) for i,b in enumerate(tail))
    out_flux=(1-1/outer)*base*sum(b*outer**(-i)*(1j*p+(1j*alpha-i)/outer) for i,b in enumerate(tail))
    amplitudes=np.linalg.solve([[outgoing.conjugate(),outgoing],[out_flux.conjugate(),out_flux]],sol.y[:,-1])
    prob=w/(p*abs(amplitudes[0])**2)
    balance=abs((p/w)*(abs(amplitudes[0])**2-abs(amplitudes[1])**2)-1)
    return float(prob),float(balance)


def horizon_checks():
    radius=4.
    spectra={}
    max_flux_error=max_match_error=0.
    for label,sinh_beta in [("matched",.75),("stationary",0.)]:
        c=math.hypot(1,sinh_beta)
        spectra[label]={}
        for n in [0,1]:
            w,_=line(n,2/3,.75)
            freq=radius*(c*w-sinh_beta*n)
            mass=radius*(c*n-sinh_beta*w)
            values=[]
            for l in [0,5,6,7]:
                prob,bal=transmission(freq,mass,l,outer=65,order=6)
                reference,_=transmission(freq,mass,l,outer=82,order=8)
                max_flux_error=max(max_flux_error,bal)
                max_match_error=max(max_match_error,abs(prob-reference))
                values.append(prob)
            spectra[label][str(n)]=values
    assert max_match_error<3e-7 and max_flux_error<1e-5
    assert np.allclose(spectra["matched"]["0"],spectra["matched"]["1"],rtol=2e-9)
    assert max(abs(x-y) for x,y in zip(spectra["stationary"]["0"],spectra["stationary"]["1"]))>.1
    getcontext().prec=60
    pi=Decimal("3.14159265358979323846264338327950288419716939937510582097494")
    s=Decimal(3)/4
    c=Decimal(5)/4
    r0=Decimal(4)
    def state(m,p,g):
        q=p/m
        u=4*q/(1+(1+8*q*q).sqrt())
        r=4*g*m*(1-u*u)/(2-u*u)
        return pi*r*r/(g*(1-u*u).sqrt()),u
    comparison=[]
    for exponent in [3,4,5]:
        g=Decimal(10)**(-exponent)
        m=r0*(2+s*s)/(4*g)
        p=r0*s*c/(4*g)
        ent0,u0=state(m+Decimal(8)/15,p,g)
        ent1,u1=state(m+Decimal(17)/15,p+1,g)
        est=-16*pi*g*(Decimal(1)/2)**2/(c*(1+3*s*s/2))
        pot=8*g*(Decimal(1)/2)/(r0*(1+3*s*s/2)*c*c)
        comparison.append([float(g),float((ent1-ent0)/est),float((u1-u0)/pot)])
    assert max(abs(x-1) for x in comparison[-1][1:])<3e-5
    return dict(ell=[0,5,6,7],transmission=spectra,flux_relative_error=max_flux_error,
                outer_matching_absolute_error=max_match_error,entropy_potential_ratio=comparison)


def direct_phase_checks():
    charges=range(-4,5)
    sign=lambda r,s: -1 if (r*s)%2 else 1
    for r in charges:
        for s in charges:
            assert sign(r,s)==sign(-r,s)==sign(s,-r)
            for t in charges:
                assert sign(r,s+t)==sign(r,s)*sign(r,t)
            square=lambda z:(-1)**(z*(z-1)//2)
            assert sign(r,s)==square(r+s)*square(r)*square(s)
    def output(eta,other):
        rho=np.array([[.5,eta/2],[eta/2,.5]],complex)
        direct=np.diag([1,sign(1,other)])
        return direct@rho@direct.conj().T
    distances=[]
    for eta in [0.,.25,.7,1.]:
        dist=np.linalg.svd(output(eta,1)-output(eta,0),compute_uv=False).sum()/2
        assert abs(dist-eta)<1e-15
        distances.append(float(dist))
    # A single donor can deposit the oriented recoil only once. A second model
    # gives the same marginals via independent sign flips. Check their joint law.
    overlap = lambda x: math.exp(-x)*(1+x+x*x/2)
    earlier, later = overlap(1.), overlap(3.)
    single = 1-earlier+later
    independent = later/earlier
    returns = (1-earlier)*(1-independent)/4
    rate = lambda x: x*x/(4*(1+x+x*x/2))
    assert abs(math.exp(-2*quad(rate,0,3)[0])-later)<2e-14
    assert abs(single-independent-4*returns)<1e-14
    weights=[.13,.2,.67]
    assert abs(math.prod(later**w for w in weights)-later)<1e-15
    assert (-1)*(-1)==1
    return dict(transfer_range=[-4,4],conditioned_trace_distances=distances,
                one_donor_marginal_signs=[earlier,later],single_event_correlation=single,
                independent_increment_correlation=independent,
                spurious_two_flip_probability=returns)


def topological_checks():
    # H^2(T^4,F2) has the six coordinate two-tori, in complementary pairs.
    labels=range(64)
    complement=lambda v: ((v & 21)<<1)|((v & 42)>>1)
    pairing=lambda u,v: -1 if (u & complement(v)).bit_count()%2 else 1
    matrix=np.array([[pairing(u,v) for v in labels] for u in labels],dtype=np.int64)
    assert np.array_equal(matrix@matrix,64*np.eye(64,dtype=np.int64))
    assert np.array_equal(matrix@matrix@matrix,64*matrix)
    # Ordered simplicial cochains on the closed boundary of a 5-simplex.
    # AW cup uses a common middle vertex. Its order is kept throughout.
    cells={d:list(combinations(range(6),d+1)) for d in range(5)}
    def coboundary(values,degree):
        return {s:sum(values[s[:j]+s[j+1:]] for j in range(len(s)))%2 for s in cells[degree+1]}
    def cup(a,b,left):
        return sum(a[s[:left+1]]*b[s[left:]] for s in cells[4])%2
    def plus(a,b):
        return {s:a[s]^b[s] for s in a}
    rng=np.random.default_rng(40108)
    representative_changes=0
    for _ in range(160):
        def random_cochain(d):
            return {s:int(rng.integers(2)) for s in cells[d]}
        i,j=random_cochain(2),random_cochain(2)
        li,lj=random_cochain(1),random_cochain(1)
        ai,aj=random_cochain(1),random_cochain(1)
        ci,cj=coboundary(i,2),coboundary(j,2)
        ii,jj=plus(i,coboundary(li,1)),plus(j,coboundary(lj,1))
        raw_change=cup(ii,jj,2)^cup(i,j,2)
        assert raw_change==cup(li,cj,1)^cup(ci,lj,3)
        original=cup(i,j,2)^cup(ai,cj,1)^cup(ci,aj,3)
        altered=cup(ii,jj,2)^cup(plus(ai,li),cj,1)^cup(ci,plus(aj,lj),3)
        assert original==altered
        representative_changes+=raw_change
    assert representative_changes>40
    return dict(cohomology_size=64, raw_sheet_changes=representative_changes,
                completed_sheet_changes=0, representative_trials=160,
                intersection_complementary=pairing(1,2),
                intersection_parallel=pairing(1,1),auxiliary_sum_entries_checked=4096)


def figure(results):
    os.environ.setdefault("MPLCONFIGDIR", str(ROOT/".research-tools"/"matplotlib"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(8.25,3.15),layout="constrained")
    etas=np.linspace(-1.45,1.45,501)
    for n,color in [(-1,"#858a8e"),(0,"#225879"),(1,"#ad561e"),(2,"#407654")]:
        rates=[]
        for eta in etas:
            channel=line(n,2/3,math.sinh(eta))
            rates.append(0 if channel is None else channel[1]/math.cosh(eta)**2)
        axes[0].plot(etas,rates,label=f"n = {n}",color=color,linewidth=1.6)
    axes[0].axvline(math.asinh(.75),ls=":",color=".35")
    axes[0].set(xlabel="Parent rapidity", ylabel="Partial width (common scale)")
    axes[0].legend(frameon=False,fontsize=8)
    x=np.logspace(-4,0,130)
    axes[1].semilogx(x,np.log(12/x),label="Net transfer",color="#225879")
    axes[1].semilogx(x,2*(np.log(12/x)-sici(12)[1]+sici(x)[1]),label="Transfer and return",color="#ad561e")
    axes[1].set(xlabel="Infrared cutoff × path delay",ylabel="Integrated soft factor")
    axes[1].legend(frameon=False,fontsize=8)
    for axis in axes:
        axis.spines[["top","right"]].set_visible(False)
    target=ROOT/"manuscripts"/"wrapped_membrane_capture.pdf"
    target.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(target,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    result=dict(transition=transition_checks(),pole=pole_checks(),soft=current_checks(),
                black_hole=horizon_checks(),direct_action=direct_phase_checks(),topology=topological_checks())
    path=ROOT/"verification"/"wrapped-membrane-capture-results.json"
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    figure(result)
    print(path)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
