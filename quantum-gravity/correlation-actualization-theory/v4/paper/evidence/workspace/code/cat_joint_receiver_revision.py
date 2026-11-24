"""A common-source effective scattering experiment and the checks used in CAT, revision two."""
from fractions import Fraction as F
from itertools import product
from math import sqrt, pi
from pathlib import Path
import argparse
import json
import numpy as np
from scipy.stats import beta, binom

I2=np.eye(2)
SX=np.array([[0,1],[1,0]],complex)
SY=np.array([[0,-1j],[1j,0]])
SZ=np.diag([1.,-1.])

def close(x,y):
    np.testing.assert_allclose(x,y,atol=3e-12,rtol=4e-13)

def clock():
    # Directly sum both Lorentz index orders, then independently form the clock energy.
    tensor=[]; clock_values=[]; euclidean=[]; only_velocity=[]
    for t in 2*pi*np.arange(128)/128:
        x=np.cos(t)*SX; y=.5*np.sin(t)*SZ
        velocities=(-np.sin(t)*SX,.5*np.cos(t)*SZ)
        f01,f02=(-1j*v for v in velocities); f12=x@y-y@x
        tr=lambda m: np.trace(m).real
        contraction=(-2*tr(f01@f01)-2*tr(f02@f02)+2*tr(f12@f12))/4
        kinetic=sum(tr(v@v) for v in velocities)/2
        magnetic=-tr(f12@f12)/2
        tensor.append(contraction);clock_values.append(kinetic-magnetic)
        euclidean.append(kinetic+magnetic);only_velocity.append(.5*np.sin(t)**2)
    close(tensor,clock_values);close(np.mean(clock_values),.5);close(np.mean(euclidean),.75)
    integral=2*pi*np.mean(only_velocity);close(integral,pi/2)
    return dict(one_coordinate_periodic_action=integral,two_matrix_lorentzian_density=np.mean(tensor),
                two_matrix_euclidean_density=np.mean(euclidean))

def index_gate():
    probes=(SX,SY,SZ)
    values=[]
    for y in (2.,.5):
        d=sum(np.kron(s,s) for s in probes)-y*np.kron(SZ,I2)
        eig=np.linalg.eigvalsh(d)
        expected=sorted([1-y,1+y,-1-sqrt(4+y*y),-1+sqrt(4+y*y)])
        close(eig,expected)
        values.append(int(np.sign(eig).sum()/2))
    assert values==[0,1]
    return values

def amplitude(n, pos):
    v=np.zeros(n,complex);v[pos]=1
    return v

def kron(xs):
    out=np.ones(1,complex)
    for x in xs:out=np.kron(out,x)
    return out

def contacts(kappa, r=F(3,4)):
    # Local input modes 0 bright, 1 absorbed, 2 incident orthogonal polarization.
    # Directions and energies of the four flying inputs are common to both terms.
    p=4*kappa**2/(1+kappa**2)**2
    g=float(kappa)
    u=np.eye(3,dtype=complex)
    u[:2,:2]=np.linalg.solve(I2+1j*g*SX,I2-1j*g*SX)
    close(u.conj().T@u,np.eye(3))
    initial=(sqrt(r)*kron([amplitude(3,i) for i in (0,0,0,2)])
             +1j*sqrt(1-r)*kron([amplitude(3,i) for i in (0,2,0,0)]))
    joint=kron([u]*4)@initial
    laws={}
    for config,amp in zip(product(range(3),repeat=4),joint):
        clicks=tuple(int(x==1) for x in config)
        laws[clicks]=laws.get(clicks,0.)+float(abs(amp)**2)
    total=sum(laws.values());close(total,1)
    def weight(fn):return sum(w for h,w in laws.items() if fn(*h))
    values=[weight(lambda an,am,bn,bm:an==am==1),
            weight(lambda an,am,bn,bm:bm-bn==-1),
            weight(lambda an,am,bn,bm:an==am==1 and bm-bn==-1),
            weight(lambda an,am,bn,bm:bm-bn==1),
            weight(lambda an,am,bn,bm:bn==bm==0)]
    exact=[r*p*p,r*p+(1-r)*p*(1-p),r*p**3,(1-r)*p*(1-p),r*(1-p)+(1-r)*(1-p)**2]
    close(values,[float(v) for v in exact])
    # An arbitrary remote observable is unchanged by this local nonselective contact.
    project=np.diag([0,1,0]); ks=[project@u,(np.eye(3)-project)@u]
    remote=np.array([[1.,.2j],[-.2j,3.]])
    observable=np.kron(np.eye(3),remote)
    lifted=[np.kron(k,I2) for k in ks]
    close(sum(k.conj().T@observable@k for k in lifted),observable)
    return dict(kappa=str(kappa), absorption=str(p), matched_A=str(exact[0]),
                closed_B=str(exact[1]), joint=str(exact[2]), wrong_B=str(exact[3]),
                both_empty_B=str(exact[4])),laws

def exchanges():
    M=F(3); energy=F(4); mass_after_squared=M*M+2*M*energy
    assert (M+energy)**2-energy**2==mass_after_squared
    # Each source decay emits a pair (+w,-w); both ports have the same total four-vector before/after absorption.
    for direction in (1,-1):
        incident=np.array([float(energy),direction*float(energy),0.,0.])
        resting=np.array([float(M),0.,0.,0.])
        recoiling=np.r_[sqrt(float(mass_after_squared)+float(energy)**2),incident[1:]]
        close(resting+incident,recoiling)
    # Add the four emission vectors of the two opposite pairs to the final source.
    momenta=[np.array([4.,4.*j,0.,0.]) for j in (1,-1,1,-1)]
    close(np.array([30.,0.,0.,0.]),np.array([14.,0.,0.,0.])+sum(momenta))
    support_m=F(4); momentum=F(3);support_E=F(5)
    assert support_E**2==support_m**2+momentum**2
    bare=SX@SZ-SZ@SX
    assert np.linalg.norm(bare)>1
    for generator in (float(momentum)*SZ+(-float(momentum))*SZ,
                      (float(momentum)+float(support_E))*I2):
        close(SX.conj().T@generator@SX,generator)
    return dict(absorber_mass_squared=str(mass_after_squared),router_support_energy=str(support_E),
                source_pair_momentum=0, bare_swap_commutator_norm=float(np.linalg.norm(bare)))

def recovery(laws, core=True):
    # Compose the two successive radiation emissions; use a deliberately unobserved
    # which-carrier environment. The carrier remains an orthogonal accessible syndrome.
    d=2; target_dim=3*d+1; erased=target_dim-1
    a,b=F(1,2),F(2,3)
    slot_prob=[a,(1-a)*b,(1-a)*(1-b)]
    assert sum(slot_prob)==1
    rho=np.zeros((d*d,d*d),complex)
    bell=np.eye(d).reshape(-1)/sqrt(d)
    identity=np.eye(d)
    recovery_ops=[]
    for slot in range(3):
        op=np.zeros((d,target_dim),complex);op[:,slot*d:(slot+1)*d]=identity;recovery_ops.append(op)
    reset=np.zeros((d,target_dim));reset[0,erased]=1;recovery_ops.append(reset)
    total=np.zeros((d,d),complex);success=0.;gram_defect=0.
    for (an,am,bn,bm),prob in laws.items():
        if prob==0:continue
        ks=[]
        exterior=bm-bn<0
        for t,w in enumerate(slot_prob):
            scale=sqrt(prob*float(w))
            if exterior and (t!=2 or core):
                op=np.zeros((target_dim,d),complex);op[t*d:(t+1)*d,:]=scale*identity
                ks.append(op);success+=prob*float(w)
            else:
                for j in range(d):
                    op=np.zeros((target_dim,d),complex);op[erased,j]=scale;ks.append(op)
        for k in ks:
            total+=k.conj().T@k
            for rec in recovery_ops:
                v=np.kron(identity,rec@k)@bell
                rho+=np.outer(v,v.conj())
        for k in ks:
            for l in ks:
                gram=k.conj().T@l
                delta=np.linalg.norm(gram-np.trace(gram)*identity/d)
                if exterior and core:close(delta,0.)
                gram_defect=max(gram_defect,float(delta))
    close(total,identity)
    fe=float((bell.conj()@rho@bell).real)
    close(fe,success+(1-success)/4)
    return dict(core_accessible=core,accessible_weight=success,entanglement_fidelity=fe,
                maximum_history_gram_defect=gram_defect)

def logical_echo(p):
    # A common absorption rotation, followed by an ordinary logical-label tag.
    # The receiver distinguishes empty, left and right. Undo the entire ordinary circuit.
    rotation=np.array([[sqrt(1-p),-sqrt(p)],[sqrt(p),sqrt(1-p)]])
    tag=np.eye(12)
    for j in (0,1):
        i=6*j+3
        tag[[i,i+1+j]]=tag[[i+1+j,i]]
    unitary=tag@np.kron(I2,np.kron(rotation,np.eye(3)))
    ket=kron([np.ones(2)/sqrt(2),amplitude(2,0),amplitude(3,0)])
    logical=np.kron(np.ones((2,2))/2,np.eye(6))
    f_logical=0.;f_full=0.
    for label in range(3):
        proj=np.kron(np.eye(4),np.diag(amplitude(3,label)))
        out=unitary.conj().T@proj@unitary@ket
        f_logical+=np.vdot(out,logical@out).real
        f_full+=float(abs(np.vdot(ket,out))**2)
    close(f_logical,1-p/2);close(f_full,(1-p)**2+p*p/2)
    return {"p":p,"logical_return":f_logical,"all_registers_return":f_full}

def protocol():
    # Hypothetical design thresholds, not observed counts. Separate calibration,
    # reversal controls and signal trials target the same underlying preparation.
    tail=.005; cal_trials=200; cal_clicks=160; sham_trials=256
    click_lower=float(beta.ppf(tail,cal_clicks,cal_trials-cal_clicks+1))
    dark_upper=.01
    p_lower=(click_lower-dark_upper)/(1-dark_upper)
    control_error=1-tail**(1/sham_trials)
    delta=control_error+.01
    upper_cat=1-p_lower/2+delta;lower_standard=1-delta
    n=100
    return dict(calibration_confidence_each=1-tail,
                independent_click_lower=p_lower,matched_error_upper=delta,
                cat_upper=upper_cat,ordinary_lower=lower_standard,
                cat_tail_88_or_more=float(binom.sf(87,n,upper_cat)),
                ordinary_tail_85_or_less=float(binom.cdf(85,n,lower_standard)))

def main():
    states=[]
    for k in (F(0),F(1,2),F(1)):
        rece,laws=contacts(k); states.append(dict(receipts=rece,
                            full=recovery(laws),radiation_only=recovery(laws,False)))
    out=dict(signed_clock=clock(),material_index=index_gate(),exchange=exchanges(),
             preparations=states,calibration_design=protocol(),echo=[logical_echo(p) for p in (0.,.64,1.)])
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    contents=json.dumps(out,indent=2)+"\n"
    output=args.output or Path(__file__).resolve().parents[1]/"verification/cat-joint-receiver-revision-results.json"
    output.write_text(contents,"utf8")

if __name__=="__main__":main()

