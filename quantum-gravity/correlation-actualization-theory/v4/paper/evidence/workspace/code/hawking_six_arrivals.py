"""Joint material mismatch and outgoing multiplicity for six Gaussian quadrupole arrivals."""
from functools import lru_cache
from itertools import permutations
import math

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.stats import qmc


def cycle_list(p):
    seen,groups=set(),[]
    for index in range(len(p)):
        if index in seen:
            continue
        cyc=[]
        while index not in seen:
            seen.add(index)
            cyc.append(index)
            index=p[index]
        groups.append(cyc)
    return groups


@lru_cache(None)
def contractions():
    all_p=list(permutations(range(6)))
    char={(1,1,1,1):4,(1,1,2):0,(2,2):4,(1,3):-2,(4,):0}
    def partial(p):
        filtered=[[k for k in c if k>=2] for c in cycle_list(p)]
        length=tuple(sorted(len(c) for c in filtered if c))
        return 5**sum(not c for c in filtered)*char[length]
    weights=[]
    for p in all_p:
        sp=tuple(1-j if j<2 else j for j in p)
        weights.append((5**len(cycle_list(p)), (partial(p)-partial(sp))/2))
    return np.array(all_p),np.array(weights)


def joint(K):
    """Input shape (batch,6,6); output trace and trace of D P22."""
    perms,weights=contractions()
    by_class=np.prod(K[:,np.arange(6),perms],axis=2)
    ans=by_class@weights
    assert np.max(abs(ans.imag))<2e-11*max(1.,np.max(abs(ans.real)))
    return ans.real


def experiments(x, w):
    scale=sum(w)
    def amplitude(stamps):
        return np.exp(-1j*np.asarray(stamps)[...,None]*x)*np.sqrt(w/scale)
    def grams(stamps):
        a=amplitude(stamps)
        return a@a.conj().swapaxes(-1,-2)
    uncorrelated=joint(np.eye(6)[None])[0]
    common=joint(np.ones((1,6,6)))[0]
    assert abs(uncorrelated[1]/uncorrelated[0]-8/3125)<2e-15 and common[1]==0
    values=[]
    for lag in [.25,1.,4.,12.,24.]:
        times=np.array([0.,lag,lag+7.,lag+14.,lag+21.,lag+28.])
        G=grams(times)
        total,success=joint(G[None])[0]
        visibility=abs(G[0,1])**2
        values.append([lag,float(2*(1-visibility)/(5+visibility)),float(success/total)])
    def first_density(span,seed,power):
        nodes,weights=leggauss(64)
        times=(1+nodes)*span/2
        a=amplitude(times)*np.sqrt(weights*span*scale/2)[:,None]
        # Weighted feature covariance gives the exact finite-rank Nyström L.
        gram=a.conj().T@a
        unit=np.eye(len(x))+gram
        resolvent=np.linalg.inv(unit)
        void=np.exp(-5*np.linalg.slogdet(unit)[1])
        u=qmc.Sobol(5,scramble=True,seed=seed).random_base2(power)
        t=np.c_[np.sort(u,axis=1),np.ones(len(u))]*span
        obs=[]
        for split in np.array_split(t,max(1,len(t)//64)):
            b=amplitude(split)
            L=(b@resolvent)@b.conj().swapaxes(-1,-2)
            obs.extend(joint(L))
        mean=np.mean(obs,axis=0)*void*scale**6*span**5/math.factorial(5)
        return mean
    absolute=[]
    for span in [16.,48.]:
        trials=np.stack([first_density(span,seed,10) for seed in [41,83,107,149]])
        mean=trials.mean(axis=0)
        se=trials.std(axis=0,ddof=1)/2
        assert all(mean>0) and max(se/mean)<.035
        absolute.append(dict(u_over_rs=span,any_first_six_density_times_rs=float(mean[0]),
                             accepted_first_six_density_times_rs=float(mean[1]),
                             across_scramble_standard_errors=se.tolist()))
    # The archive comparator has an absolute tolerance for many older tables.
    # Enforce a separately scaled check on these very small positive densities.
    expected=[2.08e-30,4.80e-27]
    assert all(abs(row['accepted_first_six_density_times_rs']/ref-1)<.05
               for row,ref in zip(absolute,expected))
    return dict(separated_probability=8/3125,common_probability=0,
                physical_time_samples=values,first_six_density=absolute)
