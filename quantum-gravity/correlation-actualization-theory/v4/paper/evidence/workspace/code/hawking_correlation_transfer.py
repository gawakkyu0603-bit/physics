"""Four-graviton angular transfer in the Schwarzschild Unruh flux (one parity)."""
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from math import factorial, pi, sqrt
from pathlib import Path
import json

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigvalsh

from natural_flux_endpoints import tensor_horizon
from quadrupole_rank_witness import witness
from hawking_six_arrivals import experiments as six_arrivals
from gravitational_resonance_transfer import source_response

ROOT = Path(__file__).resolve().parents[1]
PERMS = list(permutations(range(4)))


@lru_cache(None)
def cg(j, m, l, n, k, s):
    """Integer-spin Condon--Shortley coefficient using the Racah sum."""
    if m+n != s or abs(s)>k or not abs(j-l)<=k<=j+l:
        return 0.
    f = factorial
    pref = sqrt((2*k+1)*f(j+l-k)*f(j-l+k)*f(l-j+k)/f(j+l+k+1)
                *f(j+m)*f(j-m)*f(l+n)*f(l-n)*f(k+s)*f(k-s))
    low = max(0, l-k-m, j+n-k)
    high = min(j+l-k, j-m, l+n)
    return pref*sum((-1)**v/(f(v)*f(j+l-k-v)*f(j-m-v)*f(l+n-v)
                             *f(k-l+m+v)*f(k-j-n+v)) for v in range(low, high+1))


def cycles(p):
    seen, lengths = set(), []
    for i in range(4):
        if i in seen:
            continue
        n = 0
        while i not in seen:
            seen.add(i)
            i = p[i]
            n += 1
        lengths.append(n)
    return tuple(sorted(lengths))


def weight_character(lengths):
    weights = Counter({0: 1})
    for n in lengths:
        nxt = Counter()
        for old, count in weights.items():
            for m in range(-2, 3):
                nxt[old+n*m] += count
        weights = nxt
    return weights[0]-weights[1]


def singlets():
    tensors = np.zeros((5,5,5,5,5))  # logical k, then the four magnetic numbers
    for a,b,c,d in product(range(-2,3), repeat=4):
        if a+b+c+d:
            continue
        for k in range(abs(a+b),5):
            tensors[k,a+2,b+2,c+2,d+2] = ((-1)**(k-a-b)/sqrt(2*k+1)
                *cg(2,a,2,b,k,a+b)*cg(2,c,2,d,k,c+d))
    C = tensors.reshape(5,-1)
    assert np.allclose(C@C.T, np.eye(5))
    single_error = 0.
    for site in range(1,5):
        rest = np.moveaxis(tensors,site,1).reshape(5,5,-1)
        gram = np.einsum("kmr,lnr->klmn",rest,rest)
        single_error = max(single_error,abs(gram-np.einsum("kl,mn->klmn",np.eye(5),np.eye(5))/5).max())
    assert single_error < 2e-14
    spectra = [np.linalg.svd(tensors.reshape(5**(1+s),-1)/sqrt(5),
                              compute_uv=False) for s in range(5)]
    ranks = [int(np.sum(w>1e-12)) for w in spectra]
    assert ranks == [5,25,25,5,1]
    reps = []
    for p in PERMS:
        permuted = tensors.transpose((0,)+tuple(i+1 for i in p)).reshape(5,-1)
        mat = C @ permuted.T
        assert abs(np.trace(mat)-weight_character(cycles(p)))<1e-12
        reps.append(mat)
    cross = tensors.transpose(0,1,3,2,4).reshape(5,-1)
    p = (C[0]@cross.T)**2
    assert np.allclose(p, (2*np.arange(5)+1)/25)
    return tensors,np.array(reps),dict(single_erasure_error=float(single_error),causal_bond_dimensions=ranks,
        crossed_pair_probabilities=p.tolist(),crossed_pair_echo=float(p@p),
        character_by_cycles={"".join(map(str,c)):weight_character(c) for c in sorted(set(map(cycles,PERMS)))})


def mixed_projector(reps):
    # The trivial representation occurs once. The other four dimensions are two copies of [22].
    return np.eye(5)-np.mean(reps,axis=0)


def commutant_check(reps):
    trans=[r for r,p in zip(reps,PERMS) if cycles(p)==(1,1,2)]
    tests=np.vstack([np.kron(r,np.eye(5))-np.kron(np.eye(5),r.T) for r in trans])
    dimension=int(np.sum(np.linalg.svd(tests,compute_uv=False)<1e-10))
    assert dimension==5 and np.linalg.matrix_rank(mixed_projector(reps),tol=1e-10)==4
    return dimension


def angular_block(K, reps):
    weights = np.array([np.prod(K[np.arange(4),p]) for p in PERMS])
    Z = sum(w*5**len(cycles(p)) for w,p in zip(weights,PERMS))
    block = np.einsum("p,pkl->kl", weights,reps)
    assert abs(Z.imag)<1e-10*abs(Z) and np.linalg.norm(block-block.conj().T)<1e-10*abs(Z)
    eig = eigvalsh(block/Z.real)
    assert eig[0] > -2e-14
    mixed_weight=float(np.trace(mixed_projector(reps)@block).real/Z.real)
    return Z.real, eig, max(0.,mixed_weight)


def coherence(reps):
    rows = []
    for eta in [0.,.25,.5,.75,.9,.99,1.]:
        K = (1-eta)*np.eye(4)+eta*np.ones((4,4))
        Z, eig, qubit = angular_block(K,reps)
        den = 625+750*eta**2+200*eta**3+105*eta**4
        symmetric = 1+6*eta**2+8*eta**3+9*eta**4
        mixed = (1-eta)**2*(1+2*eta+3*eta**2)
        assert abs(Z-den)<3e-12 and np.allclose(eig,[mixed/den]*4+[symmetric/den],atol=3e-15)
        rows.append(dict(overlap=eta,singlet_probability=float(sum(eig)),
                         passive_qubit_probability=qubit,full_payload_probability=float(5*max(0.,eig[0]))))
    return rows


def quadrature(n):
    # Split at the barrier and the narrow turnover; integrate the physical spectrum.
    points, weights = leggauss(n)
    xs, ws = [], []
    for a,b in [(0.,.35),(.35,.65),(.65,1.),(1.,1.6),(1.6,3.6)]:
        xs.extend((a+b+(b-a)*points)/2)
        ws.extend(weights*(b-a)/2)
    xs,ws=np.array(xs),np.array(ws)
    scattering = np.array([tensor_horizon(x,24.,7) for x in xs])
    residual = float(np.max(abs(scattering.sum(axis=1)-1)))
    assert residual<3e-8
    density = scattering[:,0]/np.expm1(4*pi*xs)
    measure=ws/(2*pi)
    entropy=5*sum(measure*(np.log1p(density)+density*np.log1p(1/density)))
    return xs,measure*density,residual,entropy


def schwarzschild(reps):
    coarse_x,coarse_w,_,coarse_entropy = quadrature(10)
    x,w,flux_error,entropy = quadrature(16)
    c_n, c_e = 5*sum(w),5*(w@x)
    assert max(abs(5*sum(coarse_w)/c_n-1),abs(5*coarse_w@coarse_x/c_e-1))<2e-5
    assert abs(coarse_entropy/entropy-1)<2e-5 and entropy>4*pi*c_e
    def kernel(times):
        phase = np.exp(-1j*np.outer(times,x))
        return (phase*w)@phase.conj().T
    sample = []
    for spacing in [.25,1.,4.,12.,24.]:
        K = kernel(spacing*np.arange(4))
        _, eig, qubit = angular_block(K/K[0,0].real, reps)
        sample.append([spacing,float(sum(eig)),float(max(0.,5*eig[0])),qubit])
    # Nyström Janossy kernel for an exclusive quartet at four fixed retarded times.
    def exclusive(order, span):
        nodes, quad = leggauss(order)
        times,quad = (nodes+1)*span/2, quad*span/2
        stamp = span*np.array([.16,.43,.69,1.])
        full = kernel(np.r_[times,stamp])
        weighted = full[:order,:order]*np.sqrt(quad[:,None]*quad[None,:])
        cross = full[order:,:order]*np.sqrt(quad)
        L = full[order:,order:]-cross@np.linalg.solve(np.eye(order)+weighted,cross.conj().T)
        logvoid = -5*np.linalg.slogdet(np.eye(order)+weighted)[1]
        scale = full[-1,-1].real
        Z,eig,qubit = angular_block(L/scale,reps)
        return np.array([np.exp(logvoid),np.exp(logvoid)*Z*scale**4,
                         np.exp(logvoid)*Z*scale**4*max(0.,5*eig[0]),np.exp(logvoid)*Z*scale**4*qubit])
    check = []
    for span in [8.,24.,48.]:
        fine=exclusive(64,span)
        assert np.allclose(fine,exclusive(45,span),rtol=3e-8,atol=1e-45)
        check.append([span,*map(float,fine)])
    def retarded_argument(delta):
        y=sqrt(1+delta)
        return y**3/3+y*y/2+y+np.log(delta/(1+y))
    span=2*(retarded_argument(1.)-retarded_argument(1e-38))
    return dict(pre_horizon_example=[float(span),float(2*c_n*span/6)],number_per_parity_times_rs=c_n,power_per_parity_times_rs2=c_e,
                mean_frequency_times_rs=c_e/c_n,flux_conservation_error=flux_error,
                thermal_entropy_flux_times_rs=entropy,radiation_entropy_over_area_loss=entropy/(4*pi*c_e),
                unrestricted_angular_capacity_fraction=float(np.log(5)/(4*pi*(c_e/c_n))),
                coarse_flux_relative_difference=float(abs(coarse_w.sum()/w.sum()-1)),
                capacity_fraction_all_quanta_in_j2=float(np.log(5)/(16*pi*(c_e/c_n))),
                quad_tail_upper_number=float(5*np.exp(-4*pi*3.6)/(8*pi*pi*(1-np.exp(-4*pi*3.6)))),
                factorial_quartet=sample,exclusive_quartet=check,six_arrivals=six_arrivals(x,w))


def oscillator(tensors, times, initial=(0,0,0)):
    """Angular Gram amplitudes with no truncation of the occupied paths."""
    cutoff = sum(initial)+8
    states = [s for s in product(range(cutoff+1),repeat=3) if sum(s)<=cutoff]
    index = {s:i for i,s in enumerate(states)}
    annih = np.zeros((3,len(states),len(states)))
    for i,s in enumerate(states):
        for j,n in enumerate(s):
            if n:
                target = list(s)
                target[j] -= 1
                annih[j,index[tuple(target)],i] = sqrt(n)
    from scipy.sparse import csr_matrix
    a = [csr_matrix(m) for m in annih]
    vectors = np.zeros((len(states),1),complex)
    vectors[index[initial],0]=1
    for t in times:
        coords = [np.exp(-1j*t)*m+np.exp(1j*t)*m.T for m in a]
        xx,yy,zz = coords
        sph = [(xx-1j*yy)/sqrt(2),zz,-(xx+1j*yy)/sqrt(2)]
        stacked = []
        for m in range(-2,3):
            res = np.zeros_like(vectors)
            for u,v in product(range(-1,2),repeat=2):
                coeff = cg(1,u,1,v,2,m) if u+v==m else 0.
                if coeff:
                    res += coeff*(sph[v+1]@(sph[u+1]@vectors))
            stacked.append(res)
        vectors = np.stack(stacked,axis=-1).reshape(len(states),-1)
    out = vectors@tensors.reshape(5,-1).T
    return out


def relative_singular_values(matrix):
    sv=np.linalg.svd(matrix,compute_uv=False)
    return (sv/sv[0]).tolist()


def port_resonance():
    # One internal return channel, two external channels; no metric length.
    G=2*np.ones((3,3))/3-np.eye(3)
    assert np.linalg.norm(G@G.T-np.eye(3))<5e-16
    s_values=[]
    for w in [1.,-1.,(-3-4j)/5]:
        resolved=G[:2,:2]+w*np.outer(G[:2,2],G[2,:2])/(1-w*G[2,2])
        relative=-resolved  # nonsinglets reflect with amplitude -1
        assert np.linalg.norm(relative.conj().T@relative-np.eye(2))<1e-15
        s_values.append([float(relative[0,0].real),float(relative[0,0].imag)])
    assert abs(complex(*s_values[-1])-(1+1j)/2)<3e-16
    r=1/3
    probabilities=[1-4/9]+[4/9*(1-r**2)*r**(2*(n-1)) for n in range(1,15)]
    assert abs(sum(probabilities)-1)<3e-14
    return dict(elastic_amplitudes=s_values,first_return_probabilities=probabilities[:5],
                selected_q=1/8,branch=1/2)


def order_test():
    diagonals = []
    for n in [2,3]:
        links=np.diag(np.ones(n-1),-1)
        ret=np.linalg.inv(np.eye(n)-links)
        v,U=np.linalg.eigh(1j*(ret-ret.T))
        diagonals.append(float(np.sum(abs(U[0,:])**2*np.maximum(v,0.))))
    assert np.allclose(diagonals,[.5,1/sqrt(3)])
    return diagonals


def make_figure(result):
    import os
    os.environ.setdefault("MPLCONFIGDIR",str(ROOT/".research-tools"/"mplconfig"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(7.1,2.85),layout="constrained")
    eta=np.linspace(0.,1.,201)
    den=625+750*eta**2+200*eta**3+105*eta**4
    r=(1-eta)**2*(1+2*eta+3*eta**2)
    axes[0].plot(eta,100*(5+6*eta**2-8*eta**3+21*eta**4)/den,color="#414b56",label="Any singlet")
    axes[0].plot(eta,100*5*r/den,color="#00796b",label="Matched five-state transfer")
    axes[0].plot(eta,100*4*r/den,color="#af512f",ls="--",label="Universal qubit transfer")
    axes[0].set(xlabel="Common temporal overlap",ylabel="Probability per quartet (%)",xlim=(0,1),ylim=(0,1.5))
    axes[0].legend(fontsize=6.8,frameon=False)
    rows=np.array(result["schwarzschild"]["factorial_quartet"])
    axes[1].semilogy(rows[:,0],rows[:,2],"-o",ms=3,color="#00796b",label="Matched five-state transfer")
    axes[1].semilogy(rows[:,0],rows[:,3],"--s",ms=3,color="#af512f",label="Universal qubit transfer")
    axes[1].set(xlabel="Arrival separation / Schwarzschild radius",ylabel="Probability per sampled quartet",xscale="log")
    axes[1].legend(fontsize=6.8,frameon=False)
    for ax in axes:
        ax.spines[["top","right"]].set_visible(False)
    dest=ROOT/"manuscripts"/"hawking_correlation_transfer.pdf"
    dest.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(dest,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    tensors,reps,angular=singlets()
    schedules = [[0.,0.,0.,0.],[0.,.23,.71,1.3],[.1,.43,1.2,2.7]]
    osc=[relative_singular_values(oscillator(tensors,t)) for t in schedules]
    assert osc[0][1]<1e-12
    # A positive sum of these Fock-state Gram matrices is a minor witness
    # for every faithful thermal state. Do not assign the test weights to the bath.
    mixed = relative_singular_values(np.vstack([oscillator(tensors,schedules[1],s)
                       for s in [(0,0,0),(1,0,0),(2,0,0),(1,1,0)]]))
    assert mixed[-1]>1e-5
    angular['permutation_commutant_dimension']=commutant_check(reps)
    result=dict(primitive_port_resonance=port_resonance(),material_resonance=source_response(),matrix_exact_rank=witness(),angular=angular,overlap=coherence(reps),schwarzschild=schwarzschild(reps),
                matrix_vacuum_singular_values=osc,matrix_occupied_minor=mixed,order_future_extension=order_test())
    make_figure(result)
    folder=ROOT/"verification"
    folder.mkdir(exist_ok=True)
    (folder/"hawking-correlation-transfer-results.json").write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print(json.dumps(result,indent=1))


if __name__=="__main__":
    main()
