"""Two transverse matrix polarizations, matter charge and a Schwarzschild tidal input.

The oscillator basis labels the exact Gauss constraint. The upper radial cutoff is
used only for time evolution. Selection rules and energy-compatible spin readings
refer to the infinite oscillator space of this projected matter sector.
"""
from dataclasses import replace
from itertools import combinations, combinations_with_replacement
from math import comb
import json
import os
from pathlib import Path

if __name__ == "__main__":
    for key in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
        os.environ[key] = "1"

import numpy as np
from scipy.integrate import solve_ivp
from scipy.sparse import block_diag, coo_matrix, diags, eye, kron

from cat_compensated_yukawa import (MASKS, SX, SY, SZ, collective, geometry,
                                    prepare, wedge)
from cat_core_multiplet import matched_caps, polarized_transfer

ROOT = Path(__file__).resolve().parents[1]
ID = np.eye(2)


def generators():
    triple = lambda a, b, c: np.kron(a, np.kron(b, c))
    return [triple(SZ, ID, ID), triple(SX, ID, ID), triple(SY, SX, ID),
            triple(SY, SY, ID), triple(SY, SZ, SX), triple(SY, SZ, SY)]


def spin_and_statistics():
    g = generators()
    unit = np.eye(8)
    for i, a in enumerate(g):
        for j, b in enumerate(g):
            np.testing.assert_allclose(a@b+b@a, 2*(i==j)*unit)
    # Check the prefactor and relative sign directly in the unreduced colour trace.
    colour=5
    g2=.16
    qx,qy=.41+.68j,-.21+.35j
    X=[]
    for q in (qx,qy):
        X.append(np.sqrt(g2/colour)*np.kron(np.array([[0,q],[q.conjugate(),0]]),np.eye(colour)))
    comm=X[0]@X[1]-X[1]@X[0]
    zplus,zminus=(qx-1j*qy)/np.sqrt(2),(qx+1j*qy)/np.sqrt(2)
    np.testing.assert_allclose(-np.trace(comm@comm).real/(2*g2),
                               g2/colour*(abs(zplus)**2-abs(zminus)**2)**2,atol=1e-15)
    spin = -1j*g[2]@g[3]
    copy = -1j*g[4]@g[5]
    # A single common momentum direction also has two inequivalent four-spinor blocks.
    momentum = .6*g[4]+.8*g[5]
    five = g[0]@g[1]@g[2]@g[3]@momentum
    for a in [*g[:4], momentum]:
        np.testing.assert_allclose(a@five, five@a)
    np.testing.assert_allclose(np.linalg.eigvalsh(five), [-1]*4+[1]*4)
    # The commutant for six independent Clifford directions is just the scalars.
    commutators = np.vstack([np.kron(unit,a)-np.kron(a.T,unit) for a in g])
    assert 64-np.linalg.matrix_rank(commutators)==1
    low = (unit+copy)/2
    grades = np.diag(np.r_[np.diag(low@spin), -np.diag(low@spin)])
    for a in (.7*g[2]+.2j*g[3], -1.3j*g[2]+.5*g[3]):
        hop = np.block([[np.zeros_like(a),a], [a.conj().T,np.zeros_like(a)]])
        np.testing.assert_allclose(grades@hop,hop@grades)
    # Count in the entire neutral, half-filled 16-orbital Fock basis (one point).
    matter = tuple(combinations(range(8),4))
    pol = np.diag(spin).real.astype(int)
    species = np.diag(copy).real.astype(int)
    sectors = {1:0,-1:0}
    responsive = {1:0,-1:0}
    bright = {1:0.,-1:0.}
    circular_vertex=(g[2]+1j*g[3])/np.sqrt(2)
    all_rates=np.zeros(2)
    for left in matter:
        for right in matter:
            # Pauli projection evaluated directly in the original sixteen orbitals.
            # Distinct source holes and target particles are orthogonal.
            rates=[np.sum(abs(circular_vertex[np.ix_([i for i in range(8) if i not in dst],src)])**2)
                   for dst,src in ((left,right),(right,left))]
            all_rates+=rates
            for sign in (1,-1):
                if sum(species[i]==1 for i in left+right)!=2:
                    continue
                if all(pol[i]==sign for i in left if species[i]==1) and all(
                        pol[i]==-sign for i in right if species[i]==1):
                    if (sum(pol[i]==-sign and species[i]==-1 for i in left)==2 and
                            sum(pol[i]==sign and species[i]==-1 for i in right)==2):
                        sectors[sign]+=1
                        good,bad=(rates if sign==1 else rates[::-1])
                        assert bad==0
                        responsive[sign]+=int(good>0)
                        bright[sign]+=good
    assert list(sectors.values())==[18,18] and responsive[1]==responsive[-1]>0
    np.testing.assert_allclose(all_rates[0],all_rates[1])
    assert abs(bright[1]-bright[-1])<1e-12
    # A fully occupied single class at half filling has no place to hop.
    filled_plus=tuple(i for i in range(8) if pol[i]==1)
    filled_minus=tuple(i for i in range(8) if pol[i]==-1)
    for mat in [g[2],g[3]]:
        assert not np.any(mat[np.ix_(filled_minus,filled_minus)])
        assert not np.any(mat[np.ix_(filled_plus,filled_plus)])
    return dict(half_filled_neutral=len(matter)**2,receivers_per_orientation=18,
                fraction_maximally_mixed=36/len(matter)**2,
                ready_at_first_order_each=responsive[1],mean_vertex_sq_selected=bright[1]/18,
                mean_vertex_sq_per_direction_all=all_rates[0]/len(matter)**2,
                commutant_dimension_six_generators=1)


def radial_matrices(length, angular, frequency):
    n = np.arange(length)
    diag = 2*n+abs(angular)+1
    off = np.sqrt((n[1:])*(n[1:]+abs(angular)))
    radius_sq = diags((off,diag,off),(-1,0,1),shape=(length,length),format="csr")/(2*frequency)
    return diag,radius_sq


def vacuum_profile(angular, initial, final, cutoff):
    """Lowest radial eigenvector in a new harmonic basis, including its normalization."""
    order = abs(angular)
    ratio = (initial-final)/(initial+final)
    prefactor = (2*np.sqrt(initial*final)/(initial+final))**(order+1)
    return prefactor*np.array([np.sqrt(comb(n+order,n))*ratio**n for n in range(cutoff+1)])


class Receiver:
    """The two mobile spin copies share two circular complex matrix oscillators."""

    def __init__(self, config, cutoff, dark_angular, start):
        self.config = config
        self.cutoff = cutoff
        self.dark = dark_angular
        pos,_ = config.prescribed(start)
        omega_sq,axial,transverse = geometry(config,pos)
        self.frequency = np.sqrt(omega_sq)
        counts = [tuple(row.count(m) for m in range(6))
                  for row in combinations_with_replacement(range(6),2)]
        lookup = {count:i for i,count in enumerate(counts)}
        charge = np.array([(mask&3).bit_count()-1 for mask in MASKS])
        self.charges = np.array(counts)@charge
        self.active = -dark_angular-self.charges
        # Build two radial shells beyond the cutoff. Crop only after squaring the quartic.
        big = cutoff+3
        unit = eye(big,format="csr")
        full = []
        full_diff = []
        harmonic = []
        for angular in self.active:
            na,ra = radial_matrices(big,angular,self.frequency)
            nd,rd = radial_matrices(big,dark_angular,self.frequency)
            active_r,dark_r = kron(ra,unit),kron(unit,rd)
            full.append(active_r+dark_r)
            difference = (active_r-dark_r).tocsr()
            full_diff.append(difference@difference)
            harmonic.extend((self.frequency*(na[:,None]+nd)).ravel())
        self.shape = (len(counts),cutoff+1,cutoff+1)
        ids = np.arange(len(counts)*big**2).reshape(len(counts),big,big)
        inside = ids[:,:cutoff+1,:cutoff+1].ravel()
        outside = np.setdiff1d(ids.ravel(),inside)
        self.harmonic = np.asarray(harmonic)[inside]
        def crop(matrix):
            columns = matrix.tocsr()[:,inside]
            return columns[inside],columns[outside]
        self.radii,self.edge_r = crop(block_diag(full,format="csr"))
        self.quartic,self.edge_quartic = crop(block_diag(full_diff,format="csr"))
        onsite = []
        for side in (0,1):
            for pauli in (SZ,SX):
                op = np.zeros((4,4),complex)
                op[2*side:2*side+2,2*side:2*side+2]=pauli
                onsite.append(collective(wedge(op),counts,lookup))
        small_radial = eye((cutoff+1)**2,format="csr")
        self.z = np.array([np.repeat(onsite[i].diagonal().real,(cutoff+1)**2) for i in (0,2)])
        self.x = [kron(onsite[i],small_radial,format="csr") for i in (1,3)]
        raising = np.zeros((4,4),complex)
        raising[:2,2:]=SY
        hop = collective(wedge(raising),counts,lookup)
        row,col,value=[],[],[]
        for target,source in zip(*np.nonzero(hop)):
            la = self.active[source]
            for radial in range(big):
                a = radial+max(la,0)
                b = radial+max(-la,0)
                for aa,bb,factor in ((a-1,b,np.sqrt(a)),(a,b+1,np.sqrt(b+1))):
                    new = min(aa,bb)
                    if factor==0 or new>=big:
                        continue
                    assert aa-bb==self.active[target]
                    col.extend(ids[source,radial,:])
                    row.extend(ids[target,new,:])
                    value.extend([hop[target,source]*factor]*big)
        raising = coo_matrix((value,(row,col)),shape=(ids.size,ids.size)).tocsr()
        self.hop,self.edge_hop = crop(raising+raising.getH())
        # Each mobile copy has one occupied lower orbital at each end; the opposite
        # class in the other species is a filled shell with zero trace energy.
        orbit = np.zeros((4,2),complex)
        for side in (0,1):
            orbit[2*side:2*side+2,side] = np.linalg.eigh(axial[side]*SZ+transverse[side]*SX)[1][:,0]
        single = [np.linalg.det(orbit[[i for i in range(4) if mask&(1<<i)],:]) for mask in MASKS]
        self.matter = np.array([single[i]*single[j]*(1 if i==j else np.sqrt(2))
                                for i,j in combinations_with_replacement(range(6),2)])
        assert np.sum(abs(self.matter[self.charges!=0])**2)<1e-24
        np.testing.assert_allclose(np.linalg.norm(self.matter),1.)

    def initial(self, radial_active=0, radial_dark=0):
        vec = np.zeros(self.shape,complex)
        vec[:,radial_active,radial_dark]=self.matter
        return vec.ravel()

    def one_quantum(self, state, freq):
        grid = state.reshape(self.shape)
        out = np.zeros_like(grid)
        for i,la in enumerate(self.active):
            if abs(la)+abs(self.dark)!=1:
                continue
            profile = np.outer(vacuum_profile(la,self.frequency,freq,self.cutoff),
                               vacuum_profile(self.dark,self.frequency,freq,self.cutoff))
            # Normalize the projected continuum vector before the finite-box reading.
            norm=np.linalg.norm(profile)
            assert 1-norm<1e-7
            profile/=norm
            out[i] = profile*np.vdot(profile,grid[i])
        return out.ravel()


def collective_masses(config,g2):
    j,n=config.j,2*config.j+1
    inertia=n*j*(j+1)/g2
    return np.array([inertia,inertia,n/g2,n/g2,1/g2,n/g2,n/g2,1/g2])


def material_gradient(j,pos,rad,zl,zr,xl,xr):
    w1,w2,c1,c2,_,r1,r2,_=pos
    radial=j*(j+1)*(w1-w2)*rad
    axial=(c1-c2)*rad
    side=(r1-r2)*rad
    return np.array([radial+j*zl,-radial+j*zr,axial-zl,-axial-zr,zl+zr,
                     side+xl,-side+xr,-xl-xr])


def propagate(basis, initial, start, stop, g2, recoil=False, return_contact=False):
    config = basis.config
    j,n = config.j,2*config.j+1
    mass = collective_masses(config,g2)
    inertia = mass[0]
    base = g2/n*basis.quartic + np.sqrt(g2/(n*basis.frequency))*basis.hop + diags(basis.harmonic)
    edge = g2/n*basis.edge_quartic + np.sqrt(g2/(n*basis.frequency))*basis.edge_hop
    position,speed = config.prescribed(start)
    size = initial.size
    def evaluate(t,s):
        pos,vel = (s[size:size+8].real,s[size+8:size+16].real) if recoil else config.prescribed(t)
        psi=s[:size]
        om2,z,x=geometry(config,pos)
        ds=om2-basis.frequency**2
        rpsi=basis.radii@psi
        xpsi=[mat@psi for mat in basis.x]
        hpsi=(base@psi+ds*rpsi+((z[0]*basis.z[0]+z[1]*basis.z[1])*psi)
              +x[0]*xpsi[0]+x[1]*xpsi[1])
        weight=abs(psi)**2
        norm=weight.sum()
        en=np.vdot(psi,hpsi).real/norm
        rad=2*np.vdot(psi,rpsi).real/norm
        zl,zr=basis.z@weight/norm
        xl,xr=[np.vdot(psi,v).real/norm for v in xpsi]
        grad=material_gradient(j,pos,rad,zl,zr,xl,xr)
        return pos,vel,hpsi,en,grad,ds
    def rhs(t,s):
        pos,vel,hpsi,en,grad,ds=evaluate(t,s)
        psi=s[:size]
        acc=-grad/mass
        acc[:2]-=2*pos[:2]**3
        loss=np.linalg.norm(edge@psi+ds*(basis.edge_r@psi))
        return np.r_[-1j*(hpsi-en*psi),vel if recoil else np.zeros(8),
                     acc if recoil else np.zeros(8),grad@vel,loss]
    def crossing(t,s):
        p=s[size:size+8].real
        return j*p[0]+p[4]-p[2]
    crossing.terminal=True
    crossing.direction=-1
    first=np.r_[initial,position,speed,0.,0.]
    sol=solve_ivp(rhs,(start,stop),first,method="DOP853",rtol=2e-9,atol=9e-13,
                  events=crossing if recoil else None)
    assert sol.success and (not recoil or len(sol.t_events[0])==1)
    end=sol.y[:,-1]
    time=sol.t[-1]
    pos,vel,hpsi,energy,_,_=evaluate(time,end)
    initial_energy=evaluate(start,first)[3]
    assert abs(energy-initial_energy-end[-2].real)<2e-6
    if recoil:
        background_change=(mass@(vel**2-speed**2)+inertia*sum(pos[:2]**4-position[:2]**4))/2
        assert abs(energy-initial_energy+background_change)<3e-6
        for sel in (slice(2,5),slice(5,8)):
            assert abs(mass[sel]@(vel[sel]-speed[sel]))<2e-8
    psi=end[:size]
    norm=np.vdot(psi,psi).real
    assert abs(norm-1)<1.5e-8
    projected=basis.one_quantum(psi,np.sqrt(geometry(config,pos)[0]))
    one=abs(projected.reshape(basis.shape))**2/norm
    full=abs(psi.reshape(basis.shape))**2/norm
    p_one=[float(one[basis.charges==q].sum()) for q in range(-2,3)]
    p_all=[float(full[basis.charges==q].sum()) for q in range(-2,3)]
    summary=dict(time=float(time),charge_probabilities=p_all,one_by_charge=p_one,
                 probability_one=sum(p_one),work=float(end[-2].real),
                 quantum_energy_change=energy-initial_energy,
                 radial_tail_amplitude=float(end[-1].real),norm_error=abs(norm-1))
    if sum(p_one)>1e-14:
        post=end.copy()
        post[:size]=projected
        hproject=evaluate(time,post)[2]
        summary["energy_change_for_sharp_one_or_other"]=-2*np.vdot(psi-projected,hproject).real/norm
    if recoil:
        summary["collective_energy_change"]=float(background_change)
    if return_contact:
        return summary, projected, (pos.copy(), vel.copy(), psi.copy())
    return summary,projected


def merged_cores(pair_probabilities, phase_difference):
    """Recovery after two microscopic routes merge into the same available history."""
    weights=np.array(pair_probabilities)/sum(pair_probabilities)
    bell=np.array([1,0,0,1],complex)/np.sqrt(2)
    routes=[np.eye(2),np.diag(np.exp(1j*np.array([phase_difference,-phase_difference])))]
    results=[]
    for overlap in (0.,.5,1.):
        tags=[np.array([1.,0.]),np.array([overlap,np.sqrt(1-overlap**2)])]
        tag_ops=[np.outer(t,t) for t in tags]
        coherence=sum(w*U[0,0]*U[1,1].conjugate()*tag for w,U,tag in zip(weights,routes,tag_ops))
        left,spectrum,right=np.linalg.svd(coherence)
        rotate=right.conj().T@left.conj().T
        control=block_diag([rotate,ID],format="csr").toarray()
        regular=np.zeros((4,4),complex)
        for w,U,t in zip(weights,routes,tags):
            encoded=np.kron(np.kron(ID,U)@bell,t)
            decoded=np.kron(ID,control)@encoded
            regular+=w*np.trace(np.outer(decoded,decoded.conj()).reshape(4,2,4,2),axis1=1,axis2=3)
        infidelity_parameter=4*np.prod(weights)*overlap**2*np.sin(phase_difference)**2
        # Rationalized to retain small deficits when the two phases are close.
        deficit=infidelity_parameter/(2*(1+np.sqrt(1-infidelity_parameter)))
        numeric=float(np.vdot(bell,regular@bell).real)
        np.testing.assert_allclose(numeric,1-deficit,atol=2e-15,rtol=0)
        np.testing.assert_allclose(2*numeric-1,spectrum.sum(),atol=5e-15,rtol=0)
        results.append(dict(ordinary_tag_overlap=overlap,bell_fidelity=numeric,deficit=deficit))
    return dict(equal_incoming_weights=True,posterior=weights.tolist(),recoveries=results)


def tidal_pair(k=.16, partner=None):
    # The receiver is an actual pair of transverse axes in the doubled gradient
    # solution. The two charged colour orientations are distinguishable modes.
    clock,coeff,_,_=matched_caps()
    incoming=np.eye(2)
    circular=np.array([1.,1j])/np.sqrt(2)
    outputs=[]
    blocks=[]
    limit=2*min(clock(-1.4),matched_caps()[3]-clock(1.4))
    assert 0<k<limit and (partner is None or 0<partner<limit)
    for strength in (0.,.08):
        R,_=polarized_transfer(clock,coeff,strength,k)
        direct=polarized_transfer(clock,coeff,strength,k,direct=True)
        amplitude=(R[:2,:2]-incoming)/2
        # The six-axis realization uses a convention with the same gradient signs.
        np.testing.assert_allclose(direct[4:6,:2],amplitude,atol=5e-11)
        real,imag=amplitude[0,0],amplitude[1,0]
        np.testing.assert_allclose(amplitude,[[real,-imag],[imag,real]],atol=3e-13)
        helicity=np.vdot(circular,amplitude@circular)
        np.testing.assert_allclose(amplitude@circular,helicity*circular,atol=3e-13)
        p=abs(helicity)**2
        second=amplitude
        if partner is not None:
            second=polarized_transfer(clock,coeff,strength,partner,direct=True)[4:6,:2]
        partner_amp=np.vdot(circular,second@circular)
        np.testing.assert_allclose(second@circular,partner_amp*circular,atol=4e-13)
        pair_prob=p*abs(partner_amp)**2
        outputs.append(dict(deformation=strength,single_received=p,phase=np.angle(helicity),
                            partner_received=abs(partner_amp)**2,partner_phase=np.angle(partner_amp),
                            both_received=pair_prob,linear_pair_positive_helicity=pair_prob/4))
        blocks.append(np.kron(amplitude,second))
    delta=abs(np.angle(np.exp(1j*(outputs[1]["phase"]-outputs[0]["phase"]))))
    one=outputs[1]["single_received"]*np.sin(delta)**2
    phase_sum=(outputs[1]["phase"]-outputs[0]["phase"]+
               outputs[1]["partner_phase"]-outputs[0]["partner_phase"])
    pair=outputs[1]["both_received"]*np.sin(phase_sum)**2
    # A second computation projects the two distinguishable outgoing charges
    # onto the Bell vector orthogonal to the first output, with no false mark.
    cat=(np.kron(circular,circular)+np.kron(circular.conj(),circular.conj()))/np.sqrt(2)
    out=[t@cat for t in blocks]
    normal=out[1]-out[0]*(np.vdot(out[0],out[1])/np.vdot(out[0],out[0]))
    np.testing.assert_allclose(np.vdot(normal,normal).real,pair,rtol=1e-8,atol=1e-21)
    assert all(4*r["single_received"]<1 for r in outputs)
    return dict(k=k,partner_k=k if partner is None else partner,states=outputs,
                maximum_k_in_numerical_interval=limit,angle_difference=delta,
                joint_phase_difference=phase_sum,
                merged=merged_cores([x["both_received"] for x in outputs],phase_sum),
                one_quantum_exclusive=one,cat_pair_exclusive=pair,
                pair_to_single_ratio=pair/one)


class MobileModes:
    """One chiral class of four occupied fermions and its circular matrix mode."""

    def __init__(self, config, cutoff, angular_initial, start, g2):
        receiver=Receiver(config,cutoff,-angular_initial,start)
        self.shape=(len(receiver.charges),cutoff+1)
        self.charges=receiver.charges
        self.angular=receiver.active
        self.frequency=receiver.frequency
        ids=np.arange(np.prod(receiver.shape)).reshape(receiver.shape)[:,:,0].ravel()
        # The hopping and spin operators do not act on the second radial index.
        self.x=[a[ids][:,ids] for a in receiver.x]
        self.z=receiver.z[:,ids]
        size=cutoff+1
        radii,quartics,numbers=[],[],[]
        for ell in self.angular:
            number,rad=radial_matrices(size+1,ell,self.frequency)
            radii.append(rad[:size,:size])
            quartics.append((rad@rad)[:size,:size])
            numbers.extend(number[:size])
        self.radius=block_diag(radii,format="csr")
        n=2*config.j+1
        self.static=(g2/n*block_diag(quartics,format="csr")+
                     np.sqrt(g2/(n*self.frequency))*receiver.hop[ids][:,ids]+
                     diags(self.frequency*np.array(numbers)))
        self.initial=np.zeros(self.shape,complex)
        self.initial[:,0]=receiver.matter

    def operators(self, omega_sq, z, x):
        return (self.static+(omega_sq-self.frequency**2)*self.radius+
                diags(z[0]*self.z[0]+z[1]*self.z[1])+x[0]*self.x[0]+x[1]*self.x[1])


def ordinary_sea(config, start, g2, cutoff, helicity, duration=None, recoil=False,
                 return_contact=False, crossing_level=0.):
    """All eight lower end states filled. Both circular polarizations exchange particles."""
    initial_angular=(helicity,-helicity) if helicity else (0,0)
    left,right=[MobileModes(config,cutoff,a,start,g2) for a in initial_angular]
    # Reflection exchanges these banks. The two complex oscillators are coupled
    # even in the absence of a real incident pair by the non-Abelian quartic term.
    first=np.outer(left.initial.ravel(),right.initial.ravel())
    d=first.size
    cross=-2*g2/(2*config.j+1)
    mass=collective_masses(config,g2)
    pos0,vel0=config.prescribed(start)
    def equation(t,vec,gradient=False):
        state=vec[:d].reshape(first.shape)
        pos=vec[d:d+8].real if recoil else config.prescribed(t)[0]
        geom=geometry(config,pos)
        hl=left.operators(*geom)
        hr=right.operators(*geom)
        lr=left.radius@state
        value=hl@state+(hr@state.T).T+cross*(right.radius@lr.T).T
        energy=np.vdot(state,value).real/np.vdot(state,state).real
        if not gradient:
            return value,energy,None
        norm=np.vdot(state,state).real
        prob=abs(state)**2
        zl,zr=(left.z@prob.sum(axis=1)+right.z@prob.sum(axis=0))/norm
        xl,xr=[np.vdot(state,a@state+(b@state.T).T).real/norm for a,b in zip(left.x,right.x)]
        rad=2*np.vdot(state,lr+(right.radius@state.T).T).real/norm
        return value,energy,material_gradient(config.j,pos,rad,zl,zr,xl,xr)
    def rhs(t,vec):
        value,energy,grad=equation(t,vec,recoil)
        deriv=-1j*(value.ravel()-energy*vec[:d])
        if not recoil:
            return deriv
        acc=-grad/mass
        acc[:2]-=2*vec[d:d+2].real**3
        return np.r_[deriv,vec[d+8:d+16].real,acc]
    def wall(t,vec):
        return config.j*vec[d].real+vec[d+4].real-vec[d+2].real-crossing_level
    wall.terminal=True
    wall.direction=-1
    initial=np.r_[first.ravel(),pos0,vel0] if recoil else first.ravel()
    end=config.wall+(.15 if recoil else 0) if duration is None else start+duration
    sol=solve_ivp(rhs,(start,end),initial,method="DOP853",rtol=2e-9,atol=1.5e-12,
                  events=wall if recoil else None)
    assert sol.success and (not recoil or len(sol.t_events[0])==1)
    stop=sol.t[-1]
    final=sol.y[:,-1]
    state=final[:d].reshape(*left.shape,*right.shape)
    norm=float(np.vdot(state,state).real)
    assert abs(norm-1)<1e-7
    pos=final[d:d+8].real if recoil else config.prescribed(stop)[0]
    om=np.sqrt(geometry(config,pos)[0])
    charges=left.charges[:,None]+right.charges
    all_charge=np.sum(abs(state)**2,axis=(1,3))/norm
    one=np.zeros_like(all_charge)
    for i,a in enumerate(left.angular):
        for j,b in enumerate(right.angular):
            if abs(a)+abs(b)!=1:
                continue
            v=vacuum_profile(a,left.frequency,om,cutoff)
            w=vacuum_profile(b,right.frequency,om,cutoff)
            one[i,j]=abs(v@state[i,:,j,:]@w)**2/norm
    result=dict(helicity_twice=2*helicity,cutoff=cutoff,clock=stop,
                one_by_charge=[float(one[charges==q].sum()) for q in range(-4,5)],
                charge_probabilities=[float(all_charge[charges==q].sum()) for q in range(-4,5)],
                probability_one=float(one.sum()),norm_error=abs(norm-1))
    if recoil:
        vel=final[d+8:d+16].real
        quantum=equation(stop,final)[1]-equation(start,initial)[1]
        field_change=(mass@(vel**2-vel0**2)+mass[0]*sum(pos[:2]**4-pos0[:2]**4))/2
        assert abs(quantum+field_change)<3e-6
        for sel in (slice(2,5),slice(5,8)):
            assert abs(mass[sel]@(vel[sel]-vel0[sel]))<2e-8
        result.update(quantum_energy_change=quantum,collective_energy_change=field_change)
    if helicity and duration is not None:
        positions,_=config.prescribed(start)
        _,z,x=geometry(config,positions)
        spinors=[np.linalg.eigh(zi*SZ+xi*SX)[1][:,0] for zi,xi in zip(z,x)]
        overlap=abs(np.linalg.det(np.column_stack((spinors[0],SY@spinors[1]))))**2
        coefficient=4*g2*overlap/((2*config.j+1)*left.frequency)
        result["short_time_ratio"]=result["probability_one"]/(coefficient*duration**2)
        assert abs(result["short_time_ratio"]-1)<.002
    if return_contact:
        velocity = final[d+8:d+16].real if recoil else config.prescribed(stop)[1]
        return result, (left, right, pos.copy(), velocity.copy(), state.ravel().copy())
    return result


def information_in_charge(probability, rows):
    """Undo each ordinary branch isometry on its physical spin and total-helicity sectors."""
    flags=[]
    for charge in (1,-1):
        flags.append(np.diag([np.sqrt(probability) if h*s==charge else 0.
                              for h in (1,-1) for s in (1,-1)]))
    flags.append(np.sqrt(1-probability)*np.eye(4))
    # Helicity and the material grade distinguish all four columns by ordinary
    # measurements. The diagonal maps use their computed norms after undoing
    # the normalized output vectors, as in a polar decomposition.
    np.testing.assert_allclose(sum(f.T@f for f in flags),np.eye(4))
    bell=np.array([1,0,0,1])/np.sqrt(2)
    bell_state=np.outer(bell,bell)
    fidelities={}
    for label,w,coherence in (("even_pure",.5,.5),("locally_mixed",.5,0.),
                              ("aligned",1.,0.),("biased_pure",.8,.4),
                              ("partly_correlated",.5,.21),("quarter_turn_key",.5,.5j)):
        key=np.array([[w,coherence],[np.conjugate(coherence),1-w]],complex)
        recovered=np.zeros((4,4),complex)
        for idx,flag in enumerate(flags):
            joint=np.kron(bell_state,key)
            kraus=np.kron(ID,flag)
            post=kraus@joint@kraus.T
            if idx<2:
                # One reversible, outcome-dependent gate clears the correlated
                # comparison spin. The reference entangled with the input is untouched.
                untie=np.eye(4)[[0,1,3,2]]
                rotate=np.kron(ID,untie)
                post=rotate@post@rotate.T
                phase=np.angle(coherence)*(1 if idx==0 else -1)
                align=np.kron(ID,np.kron(np.diag([np.exp(-1j*phase),1]),ID))
                post=align@post@align.conj().T
            recovered+=np.trace(post.reshape(4,2,4,2),axis1=1,axis2=3)
        F=float(np.vdot(bell,recovered@bell).real)
        np.testing.assert_allclose(np.trace(recovered),1.)
        np.testing.assert_allclose(F,1-probability*(1-2*abs(coherence))/2,atol=8e-15)
        fidelities[label]=F
    # A zero-total-helicity pair is a different logical sector. The even
    # material superposition averages independent, physically orthogonal sectors.
    equal_spin=np.mean([rows[name]["charge_probabilities"] for name in
                        ("cohelical_positive_memory","cohelical_negative_memory")],axis=0)
    opposite=np.mean([rows[name]["charge_probabilities"] for name in
                      ("opposite_helicities_active","opposite_helicities_other")],axis=0)
    distance=np.sum(abs(equal_spin-opposite))/2
    assert distance>1e-5
    return dict(recovered_bell_fidelities=fidelities,charge_only_distance_other_code=distance,
                unequal_helicity_charge_distribution=opposite.tolist())


def run():
    config=prepare(8,1.95)
    start=1.15
    g2=.16
    output={}
    for label,dark,ra,rd in (("cohelical_positive_memory",-1,0,0),
                             ("cohelical_negative_memory",1,0,0),
                             ("vacuum",0,0,0),("opposite_helicities_active",0,1,0),
                             ("opposite_helicities_other",0,0,1)):
        basis=Receiver(config,11,dark,start)
        sample,projected=propagate(basis,basis.initial(ra,rd),start,config.wall,g2)
        output[label]=sample
        if dark:
            assert all(value==0 for q,value in zip(range(-2,3),sample["one_by_charge"]) if q!=-dark)
            assert sample["probability_one"]>1e-5
            # Treat the sharp read at the wall as a conditional diagnostic. The
            # following energy test concerns an actual two-outcome dephasing.
            branch=projected/np.linalg.norm(projected)
            continued,_=propagate(basis,branch,config.wall,2.31,g2)
            sample["neutral_after_conditioning"]=continued["charge_probabilities"][2]
            assert 0<sample["neutral_after_conditioning"]<1
    np.testing.assert_allclose(output["cohelical_positive_memory"]["charge_probabilities"],
                               output["cohelical_negative_memory"]["charge_probabilities"][::-1],atol=2e-8)
    np.testing.assert_allclose(output["vacuum"]["one_by_charge"],output["vacuum"]["one_by_charge"][::-1],
                               atol=2e-8)
    coarse=Receiver(config,7,-1,start)
    modest,_=propagate(coarse,coarse.initial(),start,config.wall,g2)
    fine=output["cohelical_positive_memory"]
    err=max(abs(np.asarray(modest["charge_probabilities"])-fine["charge_probabilities"]))
    assert err<3e-6
    recoil=Receiver(config,11,-1,start)
    dynamic,_=propagate(recoil,recoil.initial(),start,config.wall+.15,g2,recoil=True)
    assert dynamic["one_by_charge"][1]==0 and dynamic["one_by_charge"][3]>0
    # A local mode of a complex link and its conjugate have opposite spatial
    # offsets in the time clock. They need different *positive* null momenta.
    match=prepare(32,config.wall)
    null_low=.16
    null_high=null_low+np.sqrt(2)*match.k
    mass=np.sqrt(2*null_low*null_high)
    matched=replace(match,mass=mass)
    positions,_=matched.prescribed(matched.wall)
    freq=np.sqrt(geometry(matched,positions)[0])
    matched=replace(matched,fraction=(freq+matched.gap)/(2*(matched.j+1)*matched.gap))
    np.testing.assert_allclose([(matched.gap+matched.k)/np.sqrt(2),
                                (matched.gap-matched.k)/np.sqrt(2)],[null_high,null_low])
    kinetic=Receiver(matched,11,-1,start)
    response,_=propagate(kinetic,kinetic.initial(),start,matched.wall+.15,g2,recoil=True)
    assert response["one_by_charge"][1]==0 and response["probability_one"]>0
    matched_tide=tidal_pair(null_low,null_high)
    recoil_other=Receiver(config,11,1,start)
    rev,_=propagate(recoil_other,recoil_other.initial(),start,config.wall+.15,g2,recoil=True)
    np.testing.assert_allclose([rev["time"],rev["probability_one"]],
                               [dynamic["time"],dynamic["probability_one"]],atol=2e-10)
    sample_probability=dynamic["probability_one"]
    sea=ordinary_sea(config,start,g2,7,1)
    sea_check=ordinary_sea(config,start,g2,4,-1)
    delta=float(np.max(abs(np.array(sea["charge_probabilities"])-sea_check["charge_probabilities"])))
    assert delta<2e-7 and sea["probability_one"]>1e-4
    assert abs(sea["probability_one"]-sea_check["probability_one"])<2e-7
    short=ordinary_sea(config,start,g2,3,1,duration=.0001)
    sea_dynamic=ordinary_sea(config,start,g2,6,1,recoil=True)
    sea_dynamic_other=ordinary_sea(config,start,g2,8,-1,recoil=True)
    err_recoil=abs(sea_dynamic_other["probability_one"]-sea_dynamic["probability_one"])
    err_clock=abs(sea_dynamic_other["clock"]-sea_dynamic["clock"])
    assert err_recoil<2e-8 and err_clock<1e-8
    return dict(matrix_spin=config.j,g1_squared=g2,clock_start=start,
                ordinary_filled_sea=dict(sample=sea,reflected_coarser=sea_check,short_time=short,
                                         recoil=sea_dynamic,recoil_probability_check=err_recoil,
                                         recoil_clock_check=err_clock,
                                         charge_distribution_change=delta),
                information_after_irreversible_flag=information_in_charge(sample_probability,output),
                consistent_momenta=dict(j=matched.j,separator=mass,spatial_offset=matched.k,
                                       wall_fraction=matched.fraction,tide=matched_tide,receiver=response),
                neutral_matter=spin_and_statistics(),fixed_geometry=output,recoil=dynamic,
                coarse_cutoff=7,fine_cutoff=11,charge_cutoff_change=err,
                tidal_pair=tidal_pair())


if __name__=="__main__":
    result=run()
    dest=ROOT/"verification"/"cat-helicity-memory-results.json"
    dest.write_bytes((json.dumps(result,indent=2,allow_nan=False)+"\n").encode("utf-8"))
    print("Two polarizations, Gauss, energy, spin sectors, selection and tidal transfer passed.")

