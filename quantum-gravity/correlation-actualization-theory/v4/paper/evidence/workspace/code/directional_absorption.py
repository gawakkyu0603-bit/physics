"""A retarded material receiver, spinful-orbital capture, and escaping Dirac modes.

Use from the repository or from the extracted Paper 2 workspace. All frequencies
in the exterior calculation are in units of 1/r_s, with c = hbar = G = 1.
"""
import argparse
import json
from math import atanh, ceil, comb, cos, exp, log, log1p, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, simpson
from scipy.linalg import expm
from scipy.optimize import brentq
from scipy.special import expit, lambertw, xlogy

from mixed_flux_memory import schwarzschild_return, smooth_on

ROOT = Path(__file__).resolve().parents[1]


def matched_directions():
    # Sample the old radial solver at new material locations without changing
    # the spacetime, source history or the incoming boundary condition.
    collected = {}
    def sample(n, time, h, correction, direct):
        for index in [3*n//4, n]:
            sites = np.array([index,index-1,index-2])
            radial = (3*correction[index]-4*correction[index-1]+correction[index-2])/(2*h)
            points = direct(time, sites*h)
            radial += (3*points[0]-4*points[1]+points[2])/(2*h)
            collected.setdefault((n,index), []).append(
                [time,correction[index]+points[0],radial,correction[index]])
    schwarzschild_return(sample)
    fully = -2*sqrt(6.)
    start = fully-.25
    deadline = -2*2**.25
    def dose_source(t):
        return 3*float(smooth_on((t-start)/.25))/t**2
    front, first_return = start+.25, start+.75
    light_unit = 6*4.925490947e-6
    dose = quad(dose_source, start, start+.5, points=[fully], epsabs=1e-14)[0]/sqrt(2)
    def regular_integrand(source_time, threshold):
        receiver_time=source_time+.25
        proper_scale=receiver_time**2/4*light_unit
        rate=dose_source(source_time)/(sqrt(2)*proper_scale)
        return proper_scale*rate**3/(rate**2+threshold**2)
    regular=quad(lambda t:regular_integrand(t,500.),start,start+.5,points=[fully])[0]
    travel = lambda p: quad(lambda t: p/sqrt((t*t/4)**2+p*p), first_return, deadline)[0]
    p = brentq(lambda p: travel(p)-.25, 1e-5, 4.)
    speed = p/sqrt((first_return**2/4)**2+p*p)
    duration = (first_return**3-front**3)/12*light_unit
    # Each propagator follows a straight comoving direction in flat dust slices.
    def wrong(mu):
        flight = -.75*mu+sqrt(1-.75**2*(1-mu*mu))
        return (1-.75-flight*mu)/2
    edge = []
    for n in [128,256,512]:
        for i in [3*n//4,n]:
            t,field,space,scattered = np.array(collected[n,i]).T
            time = np.gradient(field,t,edge_order=2)
            outgoing, incoming = (time-space)/2, (time+space)/2
            err = incoming**2/(outgoing**2+incoming**2+1e-100)
            if i == n:
                rate_axis = -space / ((t*t/4)*light_unit)
                pulse = {}
                for threshold in [100.,500.,1000.]:
                    interval = np.where(rate_axis < threshold)[0]
                    last = interval[-1]
                    if last+1 == len(t):
                        continue
                    onset = np.interp(threshold, rate_axis[last:last+2], t[last:last+2])
                    g = smooth_on(np.maximum(rate_axis,0)/threshold)
                    angular_rate = pi/4*np.gradient(g,t,edge_order=2)/((t*t/4)*light_unit)
                    pulse[str(int(threshold))]=dict(
                        before_cut_seconds=float((deadline**3-onset**3)*light_unit/12),
                        maximum_angular_rate=float(np.max(np.abs(angular_rate))),
                        analytic_wrong_at_cut=float(np.sin(pi/4*(1-(rate_axis[-1]/np.hypot(threshold,rate_axis[-1]))**3))**2))
                edge.append(dict(grid=n,fraction_at_deadline=float(err[-1]),
                                 outgoing=float(outgoing[-1]),incoming=float(incoming[-1]),
                                 gradient_per_second_at_cut=float(rate_axis[-1]),pulses=pulse))
            else:
                clean = (t>front+.13)&(t<first_return-.03)
                assert np.max(np.abs(scattered[clean])) < 2e-14
                assert np.max(err[clean]) < 1e-3
    assert abs(edge[-1]['fraction_at_deadline']-edge[-2]['fraction_at_deadline']) < 5e-5
    coverage = {}
    for z in [.01,1,100]:
        scaled_d=log1p(z)/z
        value=lambda d: -np.expm1(-z*d)*exp(-d)
        assert value(scaled_d)>=max(value(scaled_d*.99),value(scaled_d*1.01))
        coverage[str(z)]=value(scaled_d)
    return dict(front_eta=front,first_return_eta=first_return,deadline_eta=deadline,
                clean_seconds=duration,dose=dose,one_site_probability=-np.expm1(-dose),
                regularized_dose_at_500=regular,regularized_receipt_at_500=-np.expm1(-regular),
                min_radial_release_speed=speed,all_outward_directions_mean_wrong=quad(wrong,0,1)[0],
                matched_edge=edge,optimal_ballistic_examples=coverage)


def return_cone():
    ri=1.5
    rc=sqrt(2)
    dv=quad(lambda r:r/(sqrt(r)+1),rc,ri,epsabs=1e-14)[0]
    primitive=lambda y:2*(y**3/3-y*y/2+y-log1p(y))
    assert abs(dv-(primitive(sqrt(ri))-primitive(sqrt(rc))))<2e-15
    optical=lambda r:r+log(r-1)
    rmax=brentq(lambda r:2*(optical(r)-optical(ri))-dv,ri,2)
    rs_time=6*4.925490947e-6
    rs_length=299792458*rs_time
    separation=quad(lambda r:1/sqrt(1-1/r),ri,rmax)[0]
    return dict(last_advanced_time_rs=dv,maximum_stationary_radius_rs=rmax,
                radial_coordinate_gap_m=(rmax-ri)*rs_length,static_slice_distance_m=separation*rs_length,
                maximum_delay_seconds_at_release=dv*sqrt(1-1/ri)*rs_time,
                open_to_center_seconds=2/3*ri**1.5*rs_time)


def microcanonical():
    # Four-momentum spectral density rho(P^2); double occupations can include
    # radiation with non-collinear momenta. The comparison uses narrow momentum bins.
    report=[]
    for mass in [2.,10.,100.]:
        x,y=4.,2.
        u,v=exp(-x),exp(-y)
        w1,w2=x/(8*pi*mass),y/(8*pi*mass)
        for cosine in [-1.,0.,1.]:
            s2=mass**2-2*mass*(w1+w2)+2*w1*w2*(1-cosine)
            corr=exp(8*pi*w1*w2*(1-cosine))
            assert abs(4*pi*(s2-mass**2)-(-x-y+log(corr)))<2e-10
            z=1+u+v+u*v*corr
            p1=(u+u*v*corr)/z
            p2=(v+u*v*corr)/z
            cov=u*v*corr/z-p1*p2
            assert abs(cov-u*v*(corr-1)/z**2)<1e-16
            report.append(dict(mass=mass,cosine=cosine,occupancy_correction=p1-expit(-x),covariance=cov))
    return report


def angular_receipt():
    # Outgoing Weyl doublet: integration over the sphere is part of its
    # isometry. Recording a direction performs a rank-one spin measurement.
    pauli=[np.array([[0,1],[1,0]],complex),np.array([[0,-1j],[1j,0]]),np.diag([1.,-1.])]
    polar,weights=np.polynomial.legendre.leggauss(8)
    eye=np.eye(2)
    norm=np.zeros((2,2),complex)
    channel=np.zeros((4,4),complex)
    for u,weight in zip(polar,weights):
        for phi in 2*pi*np.arange(12)/12:
            n=[sqrt(1-u*u)*np.cos(phi),sqrt(1-u*u)*np.sin(phi),u]
            proj=(eye+sum(c*s for c,s in zip(n,pauli)))/2
            assert abs(np.linalg.det(proj))<4e-16
            norm+=weight/12*proj
            channel+=weight/12*np.kron(proj.conj(),proj)
    def apply(matrix):
        return (channel@matrix.reshape(4,order="F")).reshape((2,2),order="F")
    error=max(np.linalg.norm(norm-eye),np.linalg.norm(apply(eye)-eye),
              *(np.linalg.norm(apply(s)-s/3) for s in pauli))
    fidelity=channel.trace().real/4
    assert error<4e-15 and abs(fidelity-.5)<2e-15
    return dict(angular_points=96,operator_error=float(error),bell_fidelity=float(fidelity))


def terminal_recoil():
    # Endpoint extrapolation only. This integral uses the leading soft greybody
    # factor, the recoil cutoff, and the exact single-mode Fermi weight.
    summary=[]
    for mass in [.1,.03,.01]:
        rate=lambda y: y*y*expit(-4*pi*mass*mass*y)
        ncoef=quad(rate,0,1)[0]/(16*pi)
        ecoef=quad(lambda y:y*rate(y),0,1)[0]/(32*pi)
        ratio=quad(lambda y:sqrt(1-y)*rate(y),0,1)[0]/quad(rate,0,1)[0]
        summary.append(dict(mass=mass,number_coefficient=ncoef,power_coefficient=ecoef,
                            mean_rest_mass_fraction=ratio))
    assert abs(summary[-1]['number_coefficient']*96*pi-1)<.001
    assert abs(summary[-1]['power_coefficient']*256*pi-1)<.001
    assert abs(summary[-1]['mean_rest_mass_fraction']-16/35)<1e-4
    return dict(per_mode_number_coefficient=1/(96*pi),per_mode_power_coefficient=1/(256*pi),
                limiting_mean_mass_ratio=16/35,integrals=summary)


def hubbard():
    # Fock basis 0, up, down, double. Both bond states have exactly two fermions.
    sing = np.zeros((4,4))
    ion = np.zeros((4,4))
    sing[1,2],sing[2,1]=1/sqrt(2),-1/sqrt(2)
    ion[0,3]=ion[3,0]=1/sqrt(2)
    ident=np.eye(4)
    number=np.diag([0.,1.,1.,2.])
    spinz=np.diag([0.,.5,-.5,0.])
    spinplus=np.zeros((4,4))
    spinplus[1,2]=1.
    eye16=np.eye(16)
    tot=lambda m: np.kron(m,eye16)+np.kron(ident,np.kron(m,ident))+np.kron(eye16,m)
    records=[]
    for interaction in [-8.,0.,1.,4.,16.]:
        gap=sqrt(interaction**2+16)
        w=(1-interaction/gap)/2
        ground=sqrt(1-w)*sing+sqrt(w)*ion
        upper=sqrt(w)*sing-sqrt(1-w)*ion
        inmat=np.kron(ident,ground.reshape(16,1))
        desired=np.kron(upper.reshape(16,1),ident)
        pg = inmat@inmat.T
        pe = desired@desired.T
        q=1/gap**2
        c=(pe@pg-pg@pe)/sqrt(q*(1-q))
        u=expm(pi*c/2)
        lo=pe@inmat
        hi=u@(np.eye(64)-pe)@inmat
        # Maximal-amplitude operator tests cover arbitrary reference entanglement.
        error=max(np.linalg.norm(lo+sqrt(q)*desired),
                  np.linalg.norm(hi+sqrt(1-q)*desired),
                  *(np.linalg.norm(c@tot(m)-tot(m)@c) for m in [number,spinz,spinplus]),
                  abs(np.linalg.norm(c,2)-1))
        # Derive the vectors independently by diagonalizing the hopping Hamiltonian.
        evals,vec=np.linalg.eigh(np.array([[0.,-2],[-2,interaction]]))
        assert abs(evals[1]-evals[0]-gap)<1e-13
        assert abs(vec[1,0]**2-w)<1e-13 and error<5e-13
        identical=np.kron(ground.reshape(16,1),ident)
        g_effect=inmat.T@identical@identical.T@inmat
        assert np.allclose(np.diag(g_effect),[w*w/4,(1-w)**2/4,(1-w)**2/4,w*w/4])
        offdiag_force=ground.ravel()@ion.ravel()*(ion.ravel()@upper.ravel())
        assert abs(offdiag_force+2/gap)<1e-14
        records.append(dict(U_over_t=interaction,ionic_weight=w,receipt_weight=q,
                            spin_and_number_error=error,naive_even_odd=np.diag(g_effect)[:2].tolist()))
    return records


def horizon_series(k, angular, offset):
    # Ingoing solution with common e^{-ik r_*} divided out. Expand in sqrt(r-1).
    order=20
    a=np.zeros((order+1,len(k)),complex)
    b=np.zeros_like(a)
    a[0]=1
    coeff=[(-1)**h*comb(2*h,h)/4**h for h in range(order//2+1)]
    for n in range(1,order+1):
        terms=range((n+1)//2)
        a[n]=2*angular*sum(coeff[h]*b[n-2*h-1] for h in terms)/n
        carry=4j*k*b[n-2] if n>=2 else 0
        b[n]=(2*angular*sum(coeff[h]*a[n-2*h-1] for h in terms)+carry)/(n-4j*k)
    z=sqrt(offset)
    return np.polynomial.polynomial.polyval(z,a), np.polynomial.polynomial.polyval(z,b)


def infinity_series(k,angular,far):
    # Outgoing solution e^{ik r_*}(B,A). Expansion in inverse areal radius.
    order=18
    a=np.zeros((order+1,len(k)),complex)
    b=np.zeros_like(a)
    a[0]=1
    s=[1.]
    for n in range(1,order+1):
        s.append(s[-1]*(n-1.5)/n)
    for n in range(1,order+1):
        conv=sum(s[h]*a[n-1-h] for h in range(n))
        past=(n-2)*b[n-2] if n>=2 else 0
        b[n]=(angular*conv+(n-1)*b[n-1]-past)/(2j*k)
        mix=sum(s[h]*(n-h)*a[n-h] for h in range(1,n))
        a[n]=(-angular*b[n]-mix)/n
    y=1/far
    return np.sum(a*y**np.arange(order+1)[:,None],axis=0),np.sum(b*y**np.arange(order+1)[:,None],axis=0)


def propagate(start,k,angular,left,right,steps,sign):
    # First-order Dirac system in log(r/r_s-1); both Wronskians have unit flux.
    a,b=start
    du=(right-left)/steps
    offset=np.exp(left)
    half=np.exp(du/2)
    whole=half**2
    def rhs(q,u,v):
        w=angular*np.sqrt(q/(1+q))
        return w*v, w*u+sign*2j*k*(1+q)*v
    for _ in range(steps):
        mid=offset*half
        end=offset*whole
        a1,b1=rhs(offset,a,b)
        a2,b2=rhs(mid,a+du*a1/2,b+du*b1/2)
        a3,b3=rhs(mid,a+du*a2/2,b+du*b2/2)
        a4,b4=rhs(end,a+du*a3,b+du*b3)
        a=a+du*(a1+2*a2+2*a3+a4)/6
        b=b+du*(b1+2*b2+2*b3+b4)/6
        offset=end
    return a,b


def transmission(x,angular,scale,depth=None):
    k=np.asarray(x)/(4*pi)
    match=log(2.)
    far=np.maximum(15.,(25+angular)/k)
    at_inf=propagate(infinity_series(k,angular,far),k,angular,np.log(far-1),match,420*scale,-1)
    if depth is None:
        off=.018
        start=horizon_series(k,angular,off)
    else:
        shell=sqrt(2)
        off=lambertw((shell-1)*exp(shell-1-depth)).real
        start=(np.ones_like(k,complex),np.zeros_like(k,complex))
    ai,bi=propagate(start,k,angular,log(off),match,int(100+65*abs(match-log(off)))*scale,1)
    ao,bo=at_inf
    return 1/abs(ai*ao-bi*bo)**2


def spectrum(step,scale):
    x=np.arange(step,32+step/2,step)
    t={}
    integrals={}
    for angular in [1,2,3]:
        coarse=transmission(x,angular,scale)
        fine=transmission(x,angular,2*scale)
        trans=fine+(fine-coarse)/15
        assert trans.min()>0 and trans.max()<1.00002
        # Clamp roundoff at the top of the open channel for entropy evaluation.
        trans=np.minimum(trans,1.)
        f=expit(-x)
        p=f*trans
        ent=-xlogy(p,p)-xlogy(1-p,1-p)
        integral=lambda a:float(simpson(np.r_[0.,a],x=np.r_[0.,x]))
        i0,i1,ising,sh=map(integral,[p,x*p,(1-f)*p,ent])
        integrals[str(angular)]=dict(I0=i0,I1=i1,single_slot=ising,
                mean_x=i1/i0,passing_per_Fermi_trial=i0/log(2),
                fraction_tagged=ising/i0,spin_only_nats_per_area_nat=log(2)*ising/i1,
                full_mode_nats_per_area_nat=sh/i1,
                maximum_uniform_read_fraction=1-i1/sh,
                power_per_magnetic_mode_M2=i1/(128*pi**3))
        t[angular]=trans
    return integrals,(x,t)


def evaporation():
    coarse,_=spectrum(.125,1)
    fine,curves=spectrum(.0625,2)
    assert max(abs(coarse[k]['I1']/fine[k]['I1']-1) for k in fine)<1e-4
    x=np.array([.4,1.,2.,4.,6.,10.])
    full=transmission(x,1,3)
    cap=[]
    for depth in [0.,4.,8.,12.]:
        cut=transmission(x,1,3,depth)
        r=sqrt(2)
        off=lambertw((r-1)*exp(r-1-depth)).real
        eps=2*atanh(sqrt(off/(1+off)))
        logerr=max(abs(np.log(cut/full)))
        assert logerr<2*eps+1e-6
        cap.append(dict(depth_rs=depth,upper_log_ratio=2*eps,max_log_ratio=logerr))
    softx=np.array([.004,.008,.016])
    soft=transmission(softx,1,3)/((softx/(4*pi))**2/4)
    assert max(abs(soft-1))<.02
    return dict(integrals=fine,coarse_l1=coarse['1'],soft_ratios=soft.tolist(),ports=cap),curves


def packet_code():
    # Each representative stands for the equal superposition of all cyclic
    # rotations of its fermionic occupation bit string. The block is a mode
    # counting test; it does not assume an infinite-energy time reference.
    L,K=13,5
    full=(1<<L)-1
    def rotate(word):
        return ((word<<1)&full)|(word>>(L-1))
    candidates={}
    for w in range(1,full):
        if w.bit_count()!=K:
            continue
        orbit=[w]
        for _ in range(1,L):
            orbit.append(rotate(orbit[-1]))
        if w!=min(orbit) or any((u^w).bit_count()==2 for u in orbit[1:]):
            continue
        candidates[w]=orbit
    selected=[]
    words=set()
    for w,orbit in candidates.items():
        if any((w^u).bit_count()==2 for u in words):
            continue
        selected.append(orbit)
        words.update(orbit)
    # Independently implement all annihilation operators, including Fock signs,
    # and calculate the Gram matrix of all one-loss logical words.
    gramvec={}
    for i in range(L):
        for o,orbit in enumerate(selected):
            for w in orbit:
                if w&(1<<i):
                    row=w^(1<<i)
                    column=i*len(selected)+o
                    sign=(-1)**((w&((1<<i)-1)).bit_count())
                    gramvec.setdefault(row,{})[column]=sign
    a=np.zeros((len(gramvec),L*len(selected)),dtype=np.int64)
    for row,cols in enumerate(gramvec.values()):
        for col,value in cols.items():
            a[row,col]=value
    difference=a.T@a-K*np.eye(a.shape[1],dtype=np.int64)
    error=int(np.max(np.abs(difference)))
    assert len(selected)>1 and error==0
    return dict(modes=L,particles=K,eligible_orbits=len(candidates),
                chosen_orbits=len(selected),representatives=[min(o) for o in selected],
                full_one_loss_gram_error=error)


def figure(path,report,curves):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    x,t=curves
    fig,(a,b)=plt.subplots(1,2,figsize=(8.2,3.1),layout="constrained")
    rad=np.linspace(.5,1.,201)
    start=-2*sqrt(6.)-.25
    a.fill_between(rad,start+rad-.5,start+2-.5-rad,color="#b7d9d8",label="Outgoing signal only")
    a.plot(rad,start+rad-.5,color="#256479",label="First direct arrival")
    a.plot(rad,start+2-.5-rad,color="#964e35",label="Earliest exterior return")
    a.set(xlabel="Comoving dust radius",ylabel="Conformal time")
    a.legend(fontsize=8,frameon=False)
    f=expit(-x)
    b.plot(x,t[1]*f,color="#285d79",label="Escaping particles")
    b.plot(x,t[1]*f*(1-f),ls="--",color="#a15235",label="Tagged spin slots")
    b.set(xlim=(0,12),xlabel=r"Energy, $\omega/T_H$",ylabel="Mean occupation per mode")
    b.legend(fontsize=8,frameon=False)
    fig.savefig(path)
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    report=dict(star=matched_directions(),causal_echo=return_cone(),orbital=hubbard(),
                microcanonical=microcanonical(),code=packet_code(),terminal=terminal_recoil(),
                angular_receipt=angular_receipt())
    report["evaporation"],curves=evaporation()
    (ROOT/"verification/directional-absorption-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        figure(args.figure,report,curves)
    print("Directional receipt, complete orbital transfer and Dirac emission checked.")
