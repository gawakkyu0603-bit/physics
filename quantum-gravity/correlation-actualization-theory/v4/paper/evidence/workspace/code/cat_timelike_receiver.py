"""Timelike noncommuting matter on the same two canonical pairs as a null tube."""
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.special import ellipj, ellipk

from cat_core_multiplet import spin_matrices

ROOT=Path(__file__).resolve().parents[1]
END=np.sqrt(2)*ellipk(.5)
MOMENTUM=.6
SPEED=.25


def radius(s):
    return ellipj(np.sqrt(2)*s,.5)[1]


def velocity(s):
    sn,_,dn,_=ellipj(np.sqrt(2)*s,.5)
    return -np.sqrt(2)*sn*dn


def read_mode(mode,derivative,w):
    occupation=(abs(derivative)**2+w**2*abs(mode)**2)/(2*w)-.5
    assert occupation>=-2e-10
    return float(max(0.,occupation)),float(1-1/np.sqrt(1+max(0.,occupation)))


def finite_clock(j,offset):
    spin_length=np.sqrt(j*(j+1))
    k=1/spin_length
    bare=np.hypot(MOMENTUM,k)
    def distance(s):
        return 1+offset+SPEED*(END-s)
    def gap(s):
        return distance(s)-abs(radius(s))
    # The contact of interest occurs at the end of the first half-oscillation.
    read=brentq(gap,END-.07,END+.07,xtol=4e-15)
    assert min(gap(t) for t in np.linspace(0,read-.001,720))>0
    def omega_sq(s):
        dw=radius(s+k/2)-radius(s-k/2)
        return bare**2+(spin_length*dw)**2
    def rhs(t,q):
        return [q[1],-omega_sq(t)*q[0]]
    initial=[1/np.sqrt(2*bare)+0j,-1j*np.sqrt(bare/2)]
    sol=solve_ivp(rhs,(0,read),initial,method="DOP853",rtol=3e-12,atol=3e-14)
    assert sol.success
    v,dv=sol.y[:,-1]
    wronskian=float(abs((v.conjugate()*dv).imag+.5))
    np.testing.assert_allclose(wronskian,0.,atol=2e-11)
    n,p=read_mode(v,dv,np.sqrt(omega_sq(read)))
    local=lambda t,q:[q[1],-(bare**2+velocity(t)**2)*q[0]]
    comparison=solve_ivp(local,(0,read),initial,method="DOP853",rtol=3e-12,atol=3e-14)
    assert comparison.success
    _,local_p=read_mode(*comparison.y[:,-1],np.hypot(bare,velocity(read)))
    times=np.linspace(0,read,301)
    frequency_difference=max(abs(omega_sq(times)-bare**2-velocity(times)**2))
    assert frequency_difference<=k*k/2
    return dict(j=j,offset=offset,contact=read,amplitude=float(radius(read)),
                instantaneous_frequency=float(np.sqrt(omega_sq(read))),particles=n,
                nonempty=p,frozen_local_nonempty=local_p,frequency_squared_error=float(frequency_difference),
                uniform_frequency_squared_bound=float(k*k/2),wronskian_error=wronskian)


def coupled(j,offset,g2=1.):
    # Local limit with one normalized real colour-singlet standing mode.
    # h=C_j^2 k^2=1, and the ordinary trace per cell gives the radial inertia.
    inertia=(2*j+1)*j*(j+1)/g2
    k=1/np.sqrt(j*(j+1))
    bare=np.hypot(k,MOMENTUM)
    initial=[1.,0.,1/np.sqrt(2*bare),0.,0.,-np.sqrt(bare/2)]
    def rhs(s,y):
        w,vel,re,im,dre,dim=y
        var=re*re+im*im
        mass=inertia-var
        assert mass>0
        acceleration=(2*(re*dre+im*dim)*vel-2*inertia*w**3)/mass
        freq2=bare**2+vel**2
        return [vel,acceleration,dre,dim,-freq2*re,-freq2*im]
    def turn(s,y):
        return y[1]
    turn.direction=1
    def crossing(s,y):
        return 1+offset+SPEED*(END-s)-abs(y[0])
    crossing.direction=-1
    sol=solve_ivp(rhs,(0,END+.08),initial,dense_output=True,events=(turn,crossing),
                  method="DOP853",rtol=3e-12,atol=3e-14)
    assert sol.success and all(len(e)==1 for e in sol.t_events)
    t_turn,t_hit=[v[0] for v in sol.t_events]
    rturn,_,re,im,dre,dim=sol.sol(t_turn)
    nturn,_=read_mode(re+1j*im,dre+1j*dim,bare)
    lost=inertia*(1-rturn**4)/2
    np.testing.assert_allclose(lost,bare*nturn,rtol=3e-6,atol=6e-7)
    r,v,re,im,dre,dim=sol.sol(t_hit)
    number,prob=read_mode(re+1j*im,dre+1j*dim,np.hypot(bare,v))
    ws,vs,re,im,dre,dim=sol.sol(np.linspace(0,END+.08,101))
    mass=inertia-re*re-im*im
    energy=(mass*vs**2+inertia*ws**4+dre**2+dim**2+bare**2*(re**2+im**2))/2
    drift=np.max(abs(energy-energy[0]))/inertia
    assert drift<4e-11 and min(mass)>0
    return dict(j=j,offset=offset,g2=g2,contact=float(t_hit),turn=float(t_turn),
                radius_at_turn=float(rturn),min_kinetic_fraction=float(min(mass)/inertia),
                contact_radius=float(r),particles=number,nonempty=prob,
                work_in_mode=float(bare*nturn),work_from_matrix=float(lost),
                energy_drift_per_inertia=float(drift))


def charge(j):
    # The entire relative Pauli spectrum near the moving axial point.
    pauli=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
    J=spin_matrices(j)
    volume=(-1j*np.trace(J[0]@(J[1]@J[2]-J[2]@J[1]))).real
    np.testing.assert_allclose(volume,(2*j+1)*j*(j+1)/3)
    marks=[]
    separation=[]
    for delta in (-.01,0.,.01):
        w=radius(END+delta)
        distance=j*(1-SPEED*delta)
        H=w*sum(np.kron(p,a) for p,a in zip(pauli,J))-distance*np.kron(pauli[2],np.eye(2*j+1))
        vals=np.linalg.eigvalsh(H)
        order=np.argsort(abs(vals))
        edge=w*j+distance
        np.testing.assert_allclose(vals[order[0]],edge,atol=3e-12)
        separation.append(float(abs(vals[order[1]])))
        marks.append(None if delta==0 else int(np.sum(np.sign(vals))//2))
    assert abs(marks[2]-marks[0])==1
    return dict(j=j,half_signature=marks,other_gap_at_contact=separation[1],volume_coefficient=volume)


def main():
    finite=[finite_clock(j,o) for j,o in ((8,0.),(32,0.),(128,0.),(32,-.005),(32,.005))]
    active=[coupled(j,o,g) for j,o,g in ((8,0.,1.),(32,0.,1.),(32,-.005,1.),
                                          (32,.005,1.),(8,0.,12.),(8,0.,48.))]
    assert min(r['nonempty'] for r in finite+active)>.08
    data=dict(half_oscillation=float(END),finite_clock=finite,local_recoil=active,
              charge_checks=[charge(j) for j in (2,8,16)])
    dest=ROOT/"verification/cat-timelike-receiver-results.json"
    dest.write_text(json.dumps(data,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Checked the timelike matrix crossing, singlet excitation and work received in its local reduction.")


if __name__=="__main__":
    main()
