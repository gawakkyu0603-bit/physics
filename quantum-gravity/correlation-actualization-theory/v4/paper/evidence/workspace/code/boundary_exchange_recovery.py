"""Material charges, membrane lapse, and full-state recovery at a private boundary."""
from math import comb, cos, exp, expm1, log, pi, sin, sqrt
from pathlib import Path
import json
import numpy as np
from scipy.constants import Boltzmann, G, c, hbar, elementary_charge
from scipy.integrate import quad
from scipy.linalg import eigh, eigh_tridiagonal, toeplitz

ROOT = Path(__file__).resolve().parents[1]
OMEGA = Boltzmann*300/hbar
OCC = 1/expm1(1.)
BAND = quad(lambda y: y*y/expm1(y),1.,2.)[0]
RADIUS = 2*G*1.98847e31/(c*c)
CONTACT = 1.e-6


def occupation_weights(mobile):
    """Exact central-binomial weights of a twin-Fock input in the exchange basis."""
    den = 4**mobile
    numer = [comb(2*k,k)*comb(2*(mobile-k),mobile-k) for k in range(mobile+1)]
    assert sum(numer)==den
    return numer,den


def membrane_lapse(angles,impact,height):
    # Symmetric image pairs. Compare this representation to its Poisson sum below.
    wrapped = (np.asarray(angles)+pi)%(2*pi)-pi
    harmonic = sum((1+((wrapped+2*pi*k)/impact)**2)**-3 for k in range(-100,101))
    return (1+height*harmonic)**(-1/3)


def lapse_series(angles,impact,height):
    angles=np.asarray(angles)
    value=np.full_like(angles,3*impact/16,dtype=float)
    for j in range(1,65):
        y=j*impact
        value+=impact/8*exp(-y)*(y*y+3*y+3)*np.cos(j*angles)
    return (1+height*value)**(-1/3)


def matrix_contacts():
    # Finite search is exact. Positive longitudinal spectators can be kept in both blocks.
    first=None
    for mobile in range(1,257):
        a,d=occupation_weights(mobile)
        if 100*sum(x*x for x in a)<d*d:
            first=mobile
            break
    assert first==172
    cases=[]
    for mobile in (63,100,127,171,172,191,255):
        a,d=occupation_weights(mobile)
        p=np.array([x/d for x in a]);nodes=np.linspace(-1.,1.,mobile+1)
        # Schwinger Jx/mobile from independent, unnormalized creation and annihilation.
        m=np.arange(-mobile,mobile)
        off=np.sqrt((mobile-m)*(mobile+m+1))/(2*mobile)
        ev,eig=eigh_tridiagonal(np.zeros(2*mobile+1),off)
        w=eig[mobile]**2
        assert max(abs(ev[::2]-nodes))<3e-14 and max(abs(w[::2]-p))<3e-13
        cases.append(dict(j=mobile,active_modes=mobile+1,collision=float(p@p)))
    q=128
    levels=[]
    for impact in (1.,2.,4.,6.):
        height=.1
        angle=pi*(np.arange(q)+.5)/q
        f=lapse_series(angle,impact,height)
        assert max(abs(f-membrane_lapse(angle,impact,height)))<5e-12
        grid=lapse_series(2*pi*np.arange(8192)/8192,impact,height)
        coeff=np.fft.rfft(grid).real/len(grid)
        e,u=eigh(toeplitz(coeff[:2*q-1]));w=u[q-1]**2
        # Parity-even subspace can instead be diagonalized exactly by folding the path.
        basis=np.zeros((2*q-1,q));basis[q-1,0]=1.
        for i in range(1,q):
            basis[q-1-i,i]=basis[q-1+i,i]=1/sqrt(2)
        folded=basis.T@toeplitz(coeff[:2*q-1])@basis
        ep,up=eigh(folded);wp=up[0]**2
        assert abs(w@w-wp@wp)<2e-10 and min(np.diff(ep))>0
        levels.append(dict(impact_over_radius=impact,height=height,
                           reflected_min_gap=float(np.min(np.diff(f))),
                           reflected_span=float(np.ptp(f)),toeplitz_min_gap=float(min(np.diff(ep))),
                           toeplitz_collision=float(wp@wp),matrix_weight_error=float(abs(w@w-wp@wp))))
    z=exp(-4.)
    def c1(x):
        return x*exp(-x)*(x*x+3*x+3)/16
    tail=(1+11*z+11*z*z+z**3)/(1-z)**5-1
    hmax=1+.1*(18/16+2*c1(4)*(1+z)/(1-z)**3)
    slope=2*.03*c1(6)*(1-tail)/(3*hmax**(4/3))
    gap=2*sin(pi/q)*sin(pi/(2*q))*slope
    span=1-hmax**(-1/3)
    assert 2*1.4*OMEGA*CONTACT*gap>4
    # At fixed b/R and fixed membrane charge the strong-coupling limit is different
    # from taking R to infinity at fixed b. This explicit state remains semiclassical.
    b=60.; ns=round(.05*b**6/(32*pi*pi))
    return dict(first_bosonic_success=first,bosonic_cases=cases,physical_lapse=levels,
                derivative_tail=tail,maximum_H=hmax,derivative_floor=slope,range_ceiling=span,
                minimum_gap_128=gap,minimum_gap_boson_191=2*slope/191,
                shortest_for_w4_s=4/(2*1.4*OMEGA*gap),
                shortest_for_count2pi_s=4/(1.4*OMEGA*gap),
                max_band_frequency_error=(1/expm1(2))/(8*BAND*CONTACT*span),
                example_source_M2_units=ns,example_height=32*pi*pi*ns/b**6)


def source_supply(a,b,angle):
    """Proper time times the early solid-angle fraction, in seconds."""
    def integrand(x):
        v=1/sqrt(x)
        s2=.1**2*(1-1/x)/(x*x)
        cs=sqrt(1-s2)
        broad=s2*(1+v)/(2*(1+cs)*(1-v*cs))
        narrow=sin(angle/2)**2 if angle is not None else broad
        return sqrt(x)*min(broad,narrow)
    return RADIUS/c*quad(integrand,a,b)[0]


def matter_and_codes(matrix):
    flux=OMEGA**3*BAND/(4*pi*pi*c*c)
    density_floor=1/expm1(2)
    # For w>=4, integral_1^2 (1-cos(wy))dy>=1/2. Keep half as a frequency margin.
    spectral_floor=density_floor/(4*BAND)
    balance=.75   # includes any splitter power ratio in [1/4,3/4]
    seed_phase_min=8*1.4; seed_phase_max=16*3.2
    assert seed_phase_max*matrix["range_ceiling"]<pi
    write_floor=4/pi**2*seed_phase_min**2*matrix["derivative_floor"]**2/2
    tslot=CONTACT
    assert 1.4*OMEGA*tslot*matrix["minimum_gap_128"]>=4
    output=[]
    for name,area,length in (("person",1.7,1.7),("1 mm",pi*1e-6,.001),("0.1 mm",pi*1e-8,.0001)):
        prefix=.1*area*flux*source_supply(4,5,None)
        count=.1*area*flux*source_supply(3,4,None)
        half_angle=min(.018,.8/(2*OMEGA/c*length))
        projected=.1*area*flux*source_supply(3,4,half_angle)*cos(.4)**2
        visibility=cos(.8)*cos(.4)**2
        # Two routes: collect one ordinary mode and split it coherently, or read a pair
        # of angular apertures using only passive interference and number detection.
        coherent_exponent=balance*count*spectral_floor/(4*(1+OCC))
        direct_exponent=projected*visibility**2*spectral_floor/(8*(1+OCC)**5)
        q=192  # conservative number of populated exchange eigenmodes in these examples
        desired=1e-5
        minimum_kept=2*log(q*q/desired)/coherent_exponent
        # Markov tail union and Gram bound separately, for the partly collected example.
        retained=.01
        accepted=retained*coherent_exponent
        bad_log=log(q*(q-1)/2)-accepted/2
        gram_log=log(q-1)-accepted/2
        output.append(dict(body=name,early_before_4R=prefix,late_4R_to_3R=count,
                           new_seed_marks_lower=prefix*write_floor/(1+OCC)**2,
                           min_single_write_probability=write_floor,
                           coherence_half_angle=half_angle,projected_after_4R=projected,
                           natural_visibility_lower=visibility,passive_exponent=direct_exponent,
                           passive_error_log=log(q)-direct_exponent,
                           full_coherent_exponent=coherent_exponent,
                           sufficient_kept_fraction_for_union=minimum_kept,
                           bad_support_log_at_one_percent=bad_log,
                           gram_error_log_at_one_percent=gram_log))
    return output


def coherent_decoder():
    """Direct Choi-state check, including coherence across photon-number sectors."""
    q=3
    phases=np.arange(q)*pi/3
    numbers=(10,11)
    offsets=np.cumsum([0]+[2*(k+1) for k in numbers])
    d=2*len(numbers)
    encoded=[];logical=[]
    for r,phi in enumerate(phases):
        code=np.zeros((offsets[-1],d),dtype=complex)
        for a,k in enumerate(numbers):
            for l in range(k+1):
                amp=sqrt(comb(k,l)/2**k)*np.exp(1j*(2*l-k)*phi)
                for pol in range(2):
                    code[offsets[a]+2*l+pol,2*a+pol]=amp
        encoded.append(code)
        # Active material charge takes different values on all four input states.
        logical.append(np.diag(np.exp(-1j*phi*np.array([.32,2.14,-.94,1.7]))))
    W=np.column_stack(encoded)
    gram=W.conj().T@W
    eig,v=eigh(gram)
    iso=W@(v@np.diag(1/np.sqrt(eig))@v.conj().T)
    assert np.linalg.norm(iso.conj().T@iso-np.eye(q*d))<1e-13
    fft=np.exp(2j*pi*np.outer(np.arange(q),np.arange(q))/q)/sqrt(q)
    heralds=[]
    for n in range(q):
        stored=sum(fft[n,r]*encoded[r]@logical[r]/sqrt(q) for r in range(q))
        prob=np.trace(stored.conj().T@stored).real/d
        blocks=(iso.conj().T@stored).reshape(q,d,d)
        corrected=[logical[r].conj().T@blocks[r] for r in range(q)]
        fidelity=sum(abs(np.trace(b))**2 for b in corrected)/(d*d*prob)
        heralds.append([prob,float(fidelity)])
    max_error=(q-1)*.5**min(numbers)
    assert max(abs(eig-1))<=max_error+1.e-14 and min(x[1] for x in heralds)>.99999
    # Reading the sign too early can cost an unknown qubit; the final classical label
    # of a real exchange alone cannot distinguish plus/minus at fixed photon energy.
    m=np.array([[.2,.18,0],[.18,.35,.12],[0,.12,.6]])
    e,u=eigh(m);a=u@(np.exp(-1j*.9*e)*u[0])
    b=u@(np.exp(1j*.9*e)*u[0])
    assert max(abs(abs(a)**2-abs(b)**2))<1e-14
    wrong_order=float(sum(abs(a)**4))
    return dict(weighted_gram_error=float(max(abs(eig-1))),uniform_gram_bound=max_error,
                herald_probability_and_entanglement_fidelity=heralds,
                premature_irreversible_record_local_return=wrong_order,
                vacuum_filled_tag_overlap=1.)


def outgoing_blocks():
    from itertools import combinations
    length=8; strings=[]
    for ones in combinations(range(length),length//2):
        strings.append(tuple(int(i in ones) for i in range(length)))
    rep=lambda s:min(s[i:]+s[:i] for i in range(len(s)))
    reps=sorted({rep(s) for s in strings})
    dim=len(reps)
    # Rows indexed by (surviving string with the lost symbol removed, lost symbol).
    maxerr=0.
    for site in range(length):
        E=np.zeros((2,2**(length-1),dim))
        for l,r in enumerate(reps):
            orb={r[i:]+r[:i] for i in range(length)}
            for s in orb:
                suffix=s[:site]+s[site+1:]
                index=sum(z*2**k for k,z in enumerate(suffix))
                E[s[site],index,l]=1/sqrt(len(orb))
        for a in (0,1):
            for b in (0,1):
                expected=np.eye(dim)/2 if a==b else np.zeros((dim,dim))
                maxerr=max(maxerr,np.max(abs(E[a].T@E[b]-expected)))
    assert maxerr<1e-14
    long_size=comb(64,32)
    return dict(eight_packet_strings=len(strings),eight_packet_orbits=dim,
                erasure_matrix_error=float(maxerr),sixty_four_words=long_size,
                guaranteed_qubits_64=(long_size//64).bit_length()-1)



def other_geometries():
    from scipy.special import digamma,gammaln
    from scipy.spatial.distance import cdist
    from scipy.stats import beta as beta_dist

    spins=[]
    for degree in (64,128,133,134,160,256):
        l=np.arange(degree)
        weights=(2*l+1)/degree**2
        area=np.sqrt(l*(l+1)/(degree*degree-1))
        collision=(4*degree**2-1)/(3*degree**3)
        assert abs(weights.sum()-1)<1e-14 and abs(weights@weights-collision)<1e-15
        spins.append(dict(spin_dimension=degree,collision=collision,min_gap=float(min(np.diff(area)))))
    # Density induced on the volume fraction in a four-dimensional flat causal diamond.
    def f_density(f):
        return 3/sqrt(f)-3*sqrt(f)+3*log(f)
    assert abs(quad(f_density,0.,1.,epsabs=1e-12)[0]-1)<2e-12
    means=[]
    for atoms in (100,500,1000,2000,4000,8000,16000):
        k=np.arange(atoms)
        inverse=np.exp(gammaln(k+.5)-gammaln(k+1)+gammaln(atoms+1)-gammaln(atoms+.5))
        w=3/atoms*(inverse*(atoms-k)/(atoms+.5)+digamma(k+1)-digamma(atoms+1))
        assert abs(sum(w)-1)<1e-9
        if atoms==100:
            for idx in (1,3,10,40):
                val=quad(lambda f:f_density(f)*beta_dist.pdf(f,idx+1,atoms-idx)/atoms,0,1)[0]
                assert abs(val-w[idx])<1e-10
        means.append(dict(atoms=atoms,zero_past_weight=float(w[0]),
                          ensemble_collision_floor=float(w@w)))
    # These are examples of realized orders; Jensen's bound above is for an ensemble.
    examples=[]
    for atoms,seed in ((512,119),(512,120),(4000,119),(8000,119)):
        rng=np.random.default_rng(seed)
        s=.5*rng.random(atoms)**.25
        t=np.where(rng.random(atoms)<.5,s,1-s)
        xyz=rng.normal(size=(atoms,3))
        xyz*=((s*rng.random(atoms)**(1/3))/np.linalg.norm(xyz,axis=1))[:,None]
        n=np.empty(atoms,dtype=int)
        for first in range(0,atoms,64):
            last=min(first+64,atoms)
            dt=t[first:last,None]-t[None,:]
            r2=cdist(xyz[first:last],xyz,'sqeuclidean')
            n[first:last]=((dt>0)&(r2<dt*dt)).sum(axis=1)
        w=np.bincount(n,minlength=atoms)/atoms
        examples.append(dict(atoms=atoms,seed=seed,collision=float(w@w),
                             distinct_volumes=int(np.count_nonzero(w))))
    s=pi/(3.2*OMEGA*CONTACT)
    def close_fraction(eps):
        return min(1.,72*eps+18*eps*log(1/eps))
    finite_n=10**13; delta=1.3e-6
    finite=1/finite_n+close_fraction(s+2*delta)+4*exp(-2*(finite_n-1)*delta**2)
    return dict(loop_spins=spins,causal_mean=means,realized_sprinklings=examples,
                continuum_resolution=s,continuum_close_ceiling=close_fraction(s),
                finite_atoms=finite_n,concentration_width=delta,finite_close_ceiling=finite)


def frozen_source_checks(matrix):
    # Source motion and ordinary free dispersion bound the validity of the compact response.
    span=matrix["range_ceiling"]
    p0=next(r["collision"] for r in matrix["bosonic_cases"] if r["j"]==191)
    tolerance=(.1-sqrt(p0))*hbar/CONTACT/elementary_charge
    # The eikonal plateau of a registered neutral energy is distinct from adding BPS tension.
    # For comoving rest probes DBI and Wess-Zumino terms cancel; at small v only v^4 survives.
    v=.001
    rms_k=3.2*Boltzmann*300*sqrt((1+OCC)*4.974314e6)
    speed_width=(matrix["maximum_H"]-1)*v**4/8
    closed_ceiling=(rms_k*CONTACT*speed_width/(2*hbar))**2
    # Two same-mass blocks at fixed total momentum. Check the curvature upper bound
    # without subtracting nearly equal relativistic energies.
    bounds=[]
    for mass,step,base,n in ((2.,1.,10,3),(.5,.2,60,4),(5.,.7,40,2)):
        curv=lambda a: mass**2/(mass**2+a**2)**1.5
        p=base*step; h=n*step
        exact=quad(lambda u:(h-u)*(curv(p-u)+curv(p+u)),0,h)[0]
        ceiling=curv(p-h)*h*h
        assert 0<=exact<=ceiling
        bounds.append([exact,ceiling])
    return dict(bosonic_dispersion_eV=tolerance,BPS_speed=v,BPS_grain_nonradial_ceiling=closed_ceiling,
                pair_energy_convexity=bounds,maximum_lapse_span=span)


def main():
    matrix=matrix_contacts()
    result=dict(matrix=matrix,matter=matter_and_codes(matrix),decoder=coherent_decoder(),
                radiation=outgoing_blocks(),geometry=other_geometries(),
                frozen_source=frozen_source_checks(matrix))
    output=ROOT/'verification'/'boundary-exchange-recovery-results.json'
    output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("First bosonic sector below 1%:",matrix["first_bosonic_success"])
    for row in result["matter"]:
        print(row["body"],row["new_seed_marks_lower"],row["bad_support_log_at_one_percent"])
    print("Stored-state test:",result["decoder"]["herald_probability_and_entanglement_fidelity"])


if __name__=="__main__":
    main()
