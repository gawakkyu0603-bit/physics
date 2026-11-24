"""Fixed-sector tests for the revised scalar, observer domains and prospective echo design."""
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.stats import beta, binom

ROOT = Path(__file__).resolve().parents[1]
I = np.eye(2)
X = np.array([[0., 1.], [1., 0.]])
Z = np.diag([1., -1.])
PLUS = (I + X) / 2
MINUS = I - PLUS

def bracket(a, b):
    return a @ b - b @ a

def scalar():
    # A three-index subblock of the ten matrices: the last, spacelike index is the probe.
    background = [0.7*Z, 0.3*X]
    phi = np.array([[0, -1j], [1j, 0]])
    def parent(xs):
        signs = [-1] + [1]*(len(xs)-1)
        return sum(signs[i]*signs[j]*np.trace(bracket(a,b) @ bracket(a,b)).real
                   for i,a in enumerate(xs) for j,b in enumerate(xs))/4
    change = parent([*background,phi])-parent(background)
    analytic = sum(sign*np.trace(bracket(a,phi) @ bracket(a,phi)).real/2
                   for sign,a in zip([-1,1],background))
    t = 2*np.pi*np.arange(128)/128
    period = float(np.pi*np.mean(np.sin(t)**2))
    assert np.isclose(period,np.pi/2) and np.isclose(change,analytic) and change>0
    return dict(period=period, old_period=-period, parent_difference=float(change),
                contracted_probe=float(analytic))

def receiver():
    r,p = 0.75,0.64
    law = {}
    for na,ma,nb,mb in itertools.product(range(2), repeat=4):
        def bit(x, bright):
            return (p if x else 1-p) if bright else float(x==0)
        law[na,ma,nb,mb] = (bit(na,True)*bit(nb,True)
                            *(r*bit(ma,True)*bit(mb,False)+(1-r)*bit(ma,False)*bit(mb,True)))
    common = sum(w for (na,ma,nb,mb),w in law.items() if na)
    closed = sum(w for (na,ma,nb,mb),w in law.items() if mb-nb<0)
    joint = law[1,1,1,0]
    # On the selected histories each description embeds the same two-dimensional input once.
    inward=np.vstack((I,np.zeros_like(I)))
    surface=np.vstack((np.zeros_like(I),I))
    assert all(np.array_equal(v.T@v,I) for v in (inward,surface))
    assert np.allclose([sum(law.values()),common,closed,joint],[1,p,.5376,.196608])
    return dict(histories=len(law), common_receipt=common, b_closed=closed, joint=joint,
                inward_dimensions=[2*max(1+q,0) for q in (0,-1)])

def history_order():
    # Exact branch probabilities for two measure-and-reset instruments on the same input.
    z0=(I+Z)/2
    def reset(rho,effect):
        return np.trace(effect@rho)*I/2
    zx=np.trace(reset(reset(z0,z0),PLUS))
    xz=np.trace(reset(reset(z0,PLUS),z0))
    # The summed operations coincide even on off-diagonal inputs.
    for i,j in itertools.product(range(2),repeat=2):
        unit=np.zeros_like(I);unit[i,j]=1
        assert np.allclose(reset(unit,z0)+reset(unit,I-z0),reset(unit,PLUS)+reset(unit,MINUS))
    for left,right in itertools.product([PLUS,MINUS],[z0,I-z0]):
        a,b=np.kron(left,I),np.kron(I,right)
        assert np.array_equal(a@b,b@a)
    # An adaptive binary tree: the second operation depends on the first result.
    k0=np.diag(np.sqrt([.7,.2])); k1=np.diag(np.sqrt([.3,.8]))
    paths={(i,j):b@a for i,a in enumerate((k0,k1))
           for j,b in enumerate((PLUS,MINUS) if i==0 else (z0,I-z0))}
    fine={k:np.kron(v.conj(),v) for k,v in paths.items()}
    def total(view):
        return sum(sum(v for k,v in fine.items() if view(k)==r) for r in (0,1))
    assert np.allclose(total(lambda k:k[0]),total(lambda k:k[1]))
    assert np.allclose(sum(v.T@v for v in paths.values()),I)
    assert np.allclose([zx,xz],[.5,.25])
    return dict(z_then_x=float(zx),x_then_z=float(xz),
                adaptive_prefix_complete=True,coarse_totals_agree=True,local_outcomes_commute=True)

def readout():
    # Deliberately biased terminal effect, positive with spectrum in [0,1].
    effect=np.array([[.95,.06],[.06,.08]])
    twirled=(effect+X@effect@X)/2
    a,b=[np.trace(e@effect) for e in (PLUS,MINUS)]
    assert np.allclose(twirled,a*PLUS+b*MINUS)
    assert np.isclose(max(abs(np.linalg.eigvalsh(twirled-PLUS))), max(1-a,b))
    return dict(always_plus_control=1.,always_plus_signal=1.,ideal_signal_at_p08=.6,
                twirled_error=float(max(1-a,b)))

def experiment():
    p_l=(float(beta.ppf(.005,160,41))-.01)/.99
    def cat_tail(q):
        return float(binom.sf(87,100,q))
    def ordinary_tail(q):
        return float(binom.cdf(85,100,q))
    old=1-.005**(1/256)+.01
    weak=float(binom.sf(159,200,.64+.01*(1-.64)))
    eps=1-.0025**(1/300)
    upper=1-(p_l/2)*(1-eps)+.01
    lower=1-eps-.01
    p=8/9
    a,b=.999,.001
    click=p+.01*(1-p)
    pass_abs=float(binom.sf(159,200,click))
    qualify=pass_abs*a**300*(1-b)**300
    true_cat=(1-p/2)*a+p*b/2
    detect_cat=float(binom.cdf(85,100,true_cat))
    detect_ord=float(binom.sf(87,100,a))
    return dict(p_lower=p_l,old_error=old,old_cat_upper=1-p_l/2+old,old_ordinary_lower=1-old,
                old_cat_tail=cat_tail(1-p_l/2+old),old_ordinary_tail=ordinary_tail(1-old),
                weak_point_absorption_qualification=weak,
                reference_error=eps,cat_upper=upper,ordinary_lower=lower,
                cat_tail=cat_tail(upper),ordinary_tail=ordinary_tail(lower),
                max_cat_false_rejection=.01+cat_tail(upper),
                max_ordinary_false_rejection=.01+ordinary_tail(lower),
                true_p=p,absorption_qualification=pass_abs,all_controls_qualify=qualify,
                true_cat_signal=true_cat,true_ordinary_signal=a,
                cat_decisive_given_qualified=detect_cat,ordinary_decisive_given_qualified=detect_ord,
                cat_decisive_per_attempt=qualify*detect_cat,ordinary_decisive_per_attempt=qualify*detect_ord,
                standard_shots=900)

if __name__=="__main__":
    data=dict(scalar=scalar(),receiver=receiver(),order=history_order(),readout=readout(),design=experiment())
    dest=ROOT/"verification/cat-domain-calibration-results.json"
    dest.write_bytes((json.dumps(data,indent=2,allow_nan=False)+"\n").encode("utf8"))
    print(json.dumps(data["design"],indent=2))

