"""Cooling of D1-D5 oscillator pairs through source-resolved gravitational vertices."""
import json
from fractions import Fraction
from math import comb, exp, factorial, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.linalg import eigvalsh, expm, solve_sylvester
from scipy.sparse import bmat, csr_matrix, eye, kron
from scipy.sparse.linalg import expm_multiply

ROOT = Path(__file__).resolve().parents[1]


def occupations(total, sites):
    if sites == 1:
        return [(total,)]
    return [(first, *tail) for first in range(total+1)
            for tail in occupations(total-first, sites-1)]


def lowering(total, imbalances):
    """Rows are states after a zero-circle-momentum emission; column sums lose one pair."""
    sites = len(imbalances)
    before = occupations(total, sites)
    after = {p:i for i,p in enumerate(occupations(total-1,sites))}
    operators = np.zeros((sites,len(after),len(before)))
    for col, state in enumerate(before):
        for i, number in enumerate(state):
            if number:
                next_state = list(state)
                next_state[i] -= 1
                operators[i,after[tuple(next_state)],col] = sqrt(number*(number+imbalances[i]))
    return operators


def tagged(total, offsets, tags):
    return np.einsum("ai,ijk->ajk",tags,lowering(total,offsets))


def endpoint(total, offsets, tags, initial=None, principal_part=0.):
    """Integrate each no-emission interval to infinity on the positive eigenspace."""
    size = len(occupations(total,len(offsets)))
    rho = np.eye(size)/size if initial is None else initial
    residual = np.zeros(total+1)
    for n in range(total,0,-1):
        jumps = tagged(n,offsets,tags)
        rate = sum(j.T@j for j in jumps)
        eig, basis = np.linalg.eigh(rate)
        eig[np.abs(eig)<2e-11] = 0.
        assert min(eig)>=0
        transformed = basis.T@rho@basis
        residual[n] = np.real(transformed.diagonal()[eig==0].sum())
        poles = (eig[:,None]+eig[None,:])/2+1j*principal_part*(eig[:,None]-eig[None,:])
        prop = np.divide(transformed,poles,out=np.zeros(transformed.shape,complex),where=abs(poles)>1e-14)
        integrated = basis@prop@basis.T
        rho = sum(j@integrated@j.T for j in jumps)
    residual[0] = rho[0,0].real
    assert abs(sum(residual)-1)<2e-10 and min(residual)>-1e-10
    return residual


def distribution_checks():
    summary = []
    for sites,groups in [(2,[0,0]),(2,[0,1]),(3,[0,0,0]),(4,[0,0,1,1])]:
        tags = np.eye(max(groups)+1)[:,groups]
        count = len(set(groups))
        for total in (1,3,5):
            def multiplicity(bins,n):
                return int(n==0) if bins==0 else comb(n+bins-1,bins-1)
            weights = [multiplicity(sites-count,d)*multiplicity(count,total-d)
                       /multiplicity(sites,total) for d in range(total+1)]
            # Nonzero protected chiral momentum changes waiting times within each representation.
            offsets = list(range(sites))
            actual = endpoint(total,offsets,tags,principal_part=.27)
            assert max(abs(actual-weights))<2e-10
        summary.append(dict(sites=sites,groups=count,total=total,residual=actual.tolist()))
    unequal = endpoint(5,[0,2],np.array([[.4,1.3]]))
    assert max(abs(unequal-1/6))<1e-10
    q = .38
    # Compute the thermal joint law from conditioned integer occupations.
    max_count = 70
    total_probability = 0.
    for d in range(max_count+1):
        for e in range(max_count+1-d):
            total_probability += (d+e+1)*(1-q)**2*q**(d+e)/(d+e+1)
    assert abs(total_probability-1)<3e-14
    return summary


def trine_certificate():
    """Verify the integrated matrix equations exactly with rational numbers.
    The real (three-direction) Gram matrix is rational although individual tags need not be.
    Numerical linear algebra proposes coefficients; exact Fraction arithmetic certifies them.
    """
    tags = np.array([[1.,-.5,-.5],[0.,sqrt(3)/2,-sqrt(3)/2]])
    gram = np.array([[Fraction(1) if a==b else Fraction(-1,2) for b in range(3)]
                     for a in range(3)],dtype=object)
    rho = np.eye(10,dtype=int).astype(object)*Fraction(1,10)
    answers = {}
    for n in (3,2,1):
        bare = lowering(n,[0,0,0]).astype(int).astype(object)
        size = bare.shape[-1]
        rate = sum(gram[a,b]*(bare[a].T@bare[b]) for a in range(3) for b in range(3))
        dark = np.array([factorial(n)//np.prod([factorial(i) for i in occ]).item()
                         for occ in occupations(n,3)],dtype=object)
        projector = np.outer(dark,dark)*Fraction(1,int(dark@dark))
        assert np.all(rate@projector==0)
        complement = np.eye(size,dtype=int).astype(object)-projector
        answers[n] = (projector@rho).trace()
        shifted = rate+projector
        forcing = 2*(complement@rho@complement)
        numerical = solve_sylvester(np.asarray(shifted,float),np.asarray(shifted,float),np.asarray(forcing,float))
        exact = np.vectorize(lambda x:Fraction(float(x)).limit_denominator(10**9),otypes=[object])(numerical)
        assert np.array_equal(shifted@exact+exact@shifted,forcing)
        assert np.all(projector@exact==0)
        rho = sum(gram[a,b]*(bare[a]@exact@bare[b].T) for a in range(3) for b in range(3))
    answers[0] = rho[0,0]
    assert [answers[i] for i in range(4)]==[Fraction(1684,4225),Fraction(2547,8450),Fraction(1,5),Fraction(1,10)]
    assert max(abs(endpoint(3,[0,0,0],tags)-[float(answers[i]) for i in range(4)]))<1e-12
    return [str(answers[i]) for i in range(4)]


def dynamics(maximum, tags):
    """All occupation blocks of the trace-preserving master equation, in emitted-line units."""
    levels = [len(occupations(n,2)) for n in range(maximum+1)]
    blocks = [[None]*(maximum+1) for _ in levels]
    blocks[0][0] = csr_matrix((1,1))
    for n in range(1,maximum+1):
        jumps = [csr_matrix(j) for j in tagged(n,[0,0],tags)]
        rate = sum(j.T@j for j in jumps)
        unit = eye(levels[n],format="csr")
        blocks[n][n] = -(kron(unit,rate)+kron(rate,unit))/2
        blocks[n-1][n] = sum(kron(j,j) for j in jumps)
    return bmat(blocks,format="csr"),levels


def finite_time():
    total = 4
    sample_times = [0.,.15,.6,2.,6.,15.]
    rows = []
    for overlap in (1.,.95,.5,0.):
        tags = np.array([[1.,overlap],[0.,sqrt(1-overlap**2)]])
        generator,levels = dynamics(total,tags)
        starts = np.cumsum([0]+[m*m for m in levels])
        initial = np.zeros(starts[-1])
        dark = np.array([(-1)**k*comb(total,k) for k in range(total+1)],float)
        dark /= np.linalg.norm(dark)
        initial[starts[-2]:] = np.outer(dark,dark).ravel()
        count = np.concatenate([n*np.eye(m).ravel() for n,m in enumerate(levels)])
        trace = np.concatenate([np.eye(m).ravel() for m in levels])
        slope = count@(generator@initial)
        assert abs(slope+(1-overlap)*total**3/(2*total-1))<2e-12
        thermal_shell = initial*0
        thermal_shell[starts[-2]:] = np.eye(total+1).ravel()/(total+1)
        initial_thermal_slope = -count@(generator@thermal_shell)
        assert abs(initial_thermal_slope-total*(2*total+1)/3)<1e-11
        results=[]
        for time in sample_times:
            state=expm_multiply(time*generator,initial)
            assert abs(trace@state-1)<2e-11
            results.append([time,float(count@state),float(state[0])])
        rows.append(dict(overlap=overlap,initial_dark_rate=-float(slope),
                         initial_thermal_shell_rate=float(initial_thermal_slope),evolution=results))
    return rows


def quantum_output():
    # An orthogonal source mark distinguishes the strands but cannot tell apart
    # two conjugate metric polarizations. Their spatial trajectories remain identical.
    rows=[]
    for total in (1,3,6):
        tags=np.eye(2)
        dark=np.array([(-1)**k*comb(total,k) for k in range(total+1)],float)/sqrt(comb(2*total,total))
        initial=np.outer(dark,dark)
        transfer=endpoint(total,[0,0],tags,initial)[0]
        assert abs(transfer-1)<2e-11
        for w in (1.,.8,0.):
            # Build the joint time-integrated channel in its two spin sectors.
            cross=initial.copy()
            for n in range(total,0,-1):
                jumps=tagged(n,[0,0],tags)
                rate=sum(j.T@j for j in jumps)
                carried=solve_sylvester(rate,rate,2*cross)
                cross=w*sum(j@carried@j.T for j in jumps)
            coherence=float(cross[0,0])
            partial_transpose=np.diag([.5,0.,0.,.5])
            partial_transpose[1,2]=partial_transpose[2,1]=coherence/2
            negativity=float(-sum(min(value,0.) for value in eigvalsh(partial_transpose)))
            assert abs(negativity-w**total/2)<2e-11
            rows.append([total,w,negativity])
    return rows


def detuning_and_clocks():
    relative_detuning = .3
    loss_matrix = np.array([[-1.,-1j*relative_detuning/2],[-1j*relative_detuning/2,0.]])
    no_click = expm(.015*loss_matrix)@np.array([0.,1.])
    short_cubic = (1-np.vdot(no_click,no_click).real)/(.015**3)
    assert abs(short_cubic-relative_detuning**2/6)<.0003
    lam=np.linalg.eigvals(loss_matrix)
    population_width=float(-2*max(lam.real))
    assert abs(population_width-(1-sqrt(1-relative_detuning**2)))<1e-13
    delta_tau=2*((1.5)**1.5-1)/3
    return dict(detuning_over_linewidth=relative_detuning,slow_population_width=population_width,
                cubic_probe=float(short_cubic),available_proper_time_over_rs=delta_tau,
                linewidth_rs_for_99_percent=-np.log(.01)/delta_tau,
                fading_record_survivals=[exp(-depth) for depth in (.1,1.,3.)])



def band_energy(winding, beta_over_R):
    # Frequency R = 2h/w; strict cutoff excludes the first charged KK rest mass.
    harmonics = np.arange(1,(winding-1)//2+1)
    frequencies = 2*harmonics/winding
    return float(np.sum(frequencies/np.expm1(beta_over_R*frequencies)))


def common_harmonics():
    from math import gcd
    rows = []
    for w1,w2,beta in [(30,60,12.),(31,59,12.),(300,600,12.),(299,601,12.),(3000,6000,12.)]:
        d = gcd(w1,w2)
        resolve = band_energy(w1,beta)+band_energy(w2,beta)
        retained = band_energy(d,beta)
        grid1 = {Fraction(2*h,w1) for h in range(1,(w1-1)//2+1)}
        grid2 = {Fraction(2*h,w2) for h in range(1,(w2-1)//2+1)}
        shared = sorted(grid1 & grid2)
        expected = [Fraction(2*h,d) for h in range(1,(d-1)//2+1)]
        assert shared==expected
        equivalent = sum(float(x)/np.expm1(beta*float(x)) for x in shared)
        assert abs(retained-equivalent)<2e-12
        rows.append(dict(windings=[w1,w2],beta_over_R=beta,neutral_shared=len(shared),
                         available_energy_R=resolve,retained_energy_R=retained,
                         trapped_fraction=retained/resolve))
    return rows


def preparation():
    cases=[]
    for n in (1,4,9):
        k=n//2
        jump=tagged(n,[0,0],np.ones((1,2)))[0]
        rate=jump.T@jump
        raw=np.array([(-1)**j*comb(n,j) for j in range(n+1)],dtype=float)
        dark=raw/np.linalg.norm(raw)
        assert max(abs(jump@dark))<1e-12
        expected=np.array([(n-d)*(n+d+1) for d in range(n+1)])[::-1]
        assert max(abs(np.linalg.eigvalsh(rate)-expected))<2e-11
        initial=np.eye(n+1)[:,k]
        weight=comb(n,k)**2/comb(2*n,n)
        no_count=expm(-rate/2)@initial
        probability=float(no_count@no_count)
        fidelity=float(abs(no_count@dark)**2/probability)
        assert abs(probability*fidelity-weight)<2e-12
        assert fidelity+1e-13>=weight/(weight+(1-weight)*exp(-2*n))
        cases.append([n,k,weight,probability,fidelity])
    return cases


def private_receipts():
    """Exchange acts on two physically received records of the full matter-field state."""
    bell_a = np.array([1,0,0,1],float)/sqrt(2)
    bell_b = np.array([1,0,0,-1],float)/sqrt(2)
    projectors = [np.outer(b,b) for b in (bell_a,bell_b)]
    one = (projectors[0]+projectors[1])/2
    swap = np.eye(16).reshape(4,4,4,4).transpose(1,0,2,3).reshape(16,16)
    odd = (np.eye(16)-swap)/2
    correlated = sum(np.kron(p,p) for p in projectors)/2
    independent = np.kron(one,one)
    antisymmetric = (np.kron(bell_a,bell_b)-np.kron(bell_b,bell_a))/sqrt(2)
    cases=[]
    for name,state,expected in [
        ("same_past",correlated,0.),("independent",independent,.25),
        ("opposite_exchange",np.outer(antisymmetric,antisymmetric),1.)]:
        assert np.max(abs(np.trace(state.reshape(4,4,4,4),axis1=1,axis2=3)-one))<1e-14
        boundary = float(np.trace(odd@state))
        assert abs(boundary-expected)<1e-13
        cases.append([name,boundary])
    # All three joint records have the same single-record marginal.
    return dict(equal_marginals=cases,independent_maximally_mixed=[
        [m,1-(m+1)/2**m] for m in (2,4,8,16)])


def receipt_exposure():
    """Compare successively absorbed gravitational records after polarization transport."""
    from scipy.stats import poisson
    rows = []
    for mean_count, visibility in [(0.1,0.), (10.,0.), (10.,0.9), (10.,1.)]:
        up = (1+visibility)/2
        down = 1-up
        survival = 0.
        for number in range(80):
            symmetric = sum(up**k * down**(number-k) for k in range(number+1))
            survival += poisson.pmf(number,mean_count) * symmetric
        if visibility == 0:
            analytic = (1+mean_count/2)*exp(-mean_count/2)
        else:
            analytic = (up*exp(-mean_count*down)-down*exp(-mean_count*up))/visibility
        assert abs(analytic-survival) < 2e-14
        assert 1-survival <= poisson.sf(1,mean_count)+2e-14
        rows.append(dict(absorbed=mean_count,visibility=visibility,edge_probability=1-analytic))
    # An unknown common rotation acts identically on two physical receipts.
    plus = np.array([1.,0.])
    cross = np.array([0.,1.])
    swap = np.eye(4).reshape(2,2,2,2).transpose(1,0,2,3).reshape(4,4)
    edge = (np.eye(4)-swap)/2
    shared = sum(np.outer(np.kron(p,p),np.kron(p,p))/2 for p in (plus,cross))
    independent = np.kron(np.eye(2)/2,np.eye(2)/2)
    assert np.trace(edge@shared)==0. and np.trace(edge@independent)==0.25
    # Splitting the logical alternatives loses a relative phase, even if neither loses energy.
    bell = np.array([1.,0.,0.,1.])/sqrt(2)
    pure = np.outer(bell,bell)
    def negativity(state):
        partial = state.reshape(2,2,2,2).transpose(2,1,0,3).reshape(4,4)
        return float(np.maximum(-eigvalsh(partial),0).sum())
    marked = np.diag(np.diag(pure))
    assert abs(negativity(pure)-.5) < 1e-14 and negativity(marked)==0.
    heralded = np.array([1.,0.,0.,.5])/sqrt(1.25)
    heralded_negativity = negativity(np.outer(heralded,heralded))
    assert abs(heralded_negativity-.4)<1e-14
    return dict(filtered_reference_negativity=heralded_negativity,first_boundary_contact=rows,common_rotation_edge=0.,independent_rotation_edge=.25,
                reference_negativity_before=negativity(pure),reference_negativity_after=negativity(marked))


def exterior_geometry():
    from scipy.integrate import quad,solve_ivp
    rows=[]
    for alpha in (1e-3,1e-5):
        # Initial areal radius is one; v is the exterior advanced coordinate.
        def escape(v,y):
            return y[1]-.01*y[0]
        escape.terminal=True
        escape.direction=1
        def derivative(v,y):
            radius,offset=y
            shrink=alpha/radius**2
            return [-shrink,offset/(2*(radius+offset))+shrink]
        sol=solve_ivp(derivative,(0.,60.),[1.,0.],events=escape,rtol=2e-11,atol=1e-13,
                      max_step=.04)
        elapsed=float(sol.t_events[0][0])
        guess=2*np.log1p(.01/(2*alpha))
        assert abs(elapsed/guess-1)<.03
        final=.8
        v_stop=(1-final**3)/(3*alpha)
        proper=quad(lambda v: sqrt(2*alpha)/(1-3*alpha*v)**(1/3),0,v_stop)[0]
        assert abs(proper-(1-final**2)/sqrt(2*alpha))<2e-10
        rows.append([alpha,elapsed,float(guess),proper])
    return dict(surface_to_one_percent=rows,quadrupole_peak_over_R=(9+sqrt(17))/8)


def continuity_at_capture():
    """A radial continuation requires two actual receipts and a symmetric comparison."""
    from scipy.optimize import brentq, minimize_scalar
    def fewer_than_two(mu):
        return (1+mu)*exp(-mu)
    near = brentq(lambda mu:fewer_than_two(mu)-.01,1.,20.)
    far = brentq(lambda mu:fewer_than_two(mu)-.99,.01,1.)
    def mixed_fall(mu):
        return (1+mu/2)*exp(-mu/2)-fewer_than_two(mu)
    optimum = minimize_scalar(lambda mu:-mixed_fall(mu),bounds=(0.,12.),method="bounded")
    assert abs(optimum.x-2*np.log(4))<2e-6
    assert abs(-optimum.fun-(3+2*np.log(4))/16)<1e-12
    assert abs(fewer_than_two(near)-.01)<1e-12 and abs(fewer_than_two(far)-.99)<1e-12
    return dict(near_falling=1-fewer_than_two(10.),far_boundary=fewer_than_two(.1),
                near_threshold=near,far_threshold=far,fluence_contrast=near/far,
                inverse_square_distance_ratio=sqrt(near/far),mixed_peak_count=2*np.log(4),
                maximum_mixed_falling=-optimum.fun)


def hawking_carriers():
    # Page's coarse entropy and power coefficients for a cold neutral four-dimensional hole.
    photon_power = Fraction(33638,10000)
    graviton_power = Fraction(3836,10000)
    graviton_entropy_ratio = Fraction(13481,10000)
    photon_entropy_ratio = Fraction(15003,10000)
    tensor_ceiling = graviton_entropy_ratio * graviton_power / (photon_power+graviton_power)
    combined = tensor_ceiling + photon_entropy_ratio*photon_power/(photon_power+graviton_power)
    assert Fraction(1379,10000)<tensor_ceiling<Fraction(1381,10000)
    assert abs(float(combined)-1.4847) < .0001
    return dict(tensor_only_entropy_per_lost_BH_entropy=float(tensor_ceiling),
                total_coarse_entropy_per_lost_BH_entropy=float(combined))


def boundary_memory():
    from scipy.integrate import quad,solve_ivp
    # The fully collected exterior port is driven by a single physical time reference.
    results=[]
    for capture,release in [(1.,2.),(4.,3.),(8.,8.)]:
        norm=sqrt(1-exp(-capture))
        pulse=lambda t:exp(t/2)/norm
        sol=solve_ivp(lambda t,y:-y/2-pulse(t),(-capture,0.),[0.],dense_output=True,
                      rtol=1e-12,atol=1e-14)
        loaded=float(sol.y[0,-1]**2)
        outgoing_before=quad(lambda t:(pulse(t)+sol.sol(t)[0])**2,-capture,0.)[0]
        radiated=loaded*quad(lambda t:exp(-t),0,release)[0]
        assert abs(loaded+outgoing_before-1)<2e-11
        assert abs(radiated-(1-exp(-capture))*(1-exp(-release)))<2e-11
        results.append([capture,release,loaded,radiated,1-radiated-outgoing_before])
    # Four different frequencies; each qubit is the polarization of a single emitted pair.
    def string_state(words):
        ket=np.zeros(16)
        for word in words: ket[int(word,2)]=1/sqrt(2)
        return ket
    iso=np.column_stack([string_state(["0011","1100"]),string_state(["0101","1010"])])
    assert np.max(abs(iso.T@iso-np.eye(2)))<1e-14
    for i in range(4):
        for a in range(2):
            for b in range(2):
                left=np.moveaxis(iso[:,a].reshape((2,)*4),i,0).reshape(2,-1)
                right=np.moveaxis(iso[:,b].reshape((2,)*4),i,0).reshape(2,-1)
                assert np.max(abs(left@right.T-np.eye(2)*(a==b)/2))<1e-14
    return dict(matched_temporal_mode=results,one_bin_checked_for_all_matrix_units=True)

def main():
    rows=finite_time()
    values=dict(block_counts=distribution_checks(),trine_residual_probabilities=trine_certificate(),
                dark_packet=rows,terminal_qubit=quantum_output(),finite_clock=detuning_and_clocks(),
                winding_band=common_harmonics(),heralded_preparation=preparation(),
                receipts=private_receipts(),receipt_exposure=receipt_exposure(),boundary_geometry=exterior_geometry(),
                boundary_memory=boundary_memory(),hawking_carriers=hawking_carriers(),continuity=continuity_at_capture())
    out=ROOT/"verification"/"winding-cooling-results.json"
    out.write_text(json.dumps(values,indent=2,allow_nan=False)+"\n",encoding="utf8")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(7.7,2.9),layout="constrained")
    for row,color in zip(rows,["#434c5e","#328979","#98672a","#935273"]):
        raw=np.array(row["evolution"])
        axes[0].plot(raw[:,0],raw[:,1],".-",c=color,label=f"z = {row['overlap']:g}")
    axes[0].set(xlabel=r"Exposure $\gamma t$",ylabel="Mean pairs remaining",xlim=(-.2,15.4),ylim=(-.12,4.3))
    axes[0].legend(frameon=False,fontsize=7,ncol=2)
    emitted=np.arange(12)
    q=.6
    axes[1].bar(emitted-.17,(1-q)*q**emitted,width=.34,color="#328979",label="Common source record")
    axes[1].bar(emitted+.17,(emitted+1)*(1-q)**2*q**emitted,width=.34,color="#935273",label="Distinct source records")
    axes[1].set(xlabel="Total number emitted in the line",ylabel="Probability",xticks=range(0,12,2))
    axes[1].legend(frameon=False,fontsize=7)
    for ax in axes: ax.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts"/"winding_cooling.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    print("Thermal sector, exact trine counts, finite cooling and terminal qubit verified.")


if __name__=="__main__":
    main()
