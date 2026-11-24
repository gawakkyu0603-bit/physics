"""Gravity-driven matrix link and its two compensated fermion endpoints.

All energies and the spectral clock are in matrix units. The scalar is a complex
off-diagonal polarization. The four extreme spinor doublets share this same
oscillator. No rotating-wave approximation is used in the real-time evolution.
"""
from dataclasses import dataclass
from itertools import combinations, combinations_with_replacement
from math import factorial, prod
import json
import os
from pathlib import Path

if __name__ == "__main__":
    for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
        os.environ[variable] = "1"

import numpy as np
from scipy.integrate import solve_ivp
from scipy.sparse import coo_matrix

from cat_timelike_receiver import END, radius, velocity
from cat_core_multiplet import spin_matrices

ROOT = Path(__file__).resolve().parents[1]
SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.diag([1., -1.])
MASKS = tuple(sum(1 << i for i in occupied) for occupied in combinations(range(4), 2))


@dataclass(frozen=True)
class Preparation:
    j: int
    wall: float
    k: float
    mass: float
    fraction: float
    point_at_wall: float
    inward_speed: float

    @property
    def gap(self):
        return float(np.hypot(self.mass, self.k))

    def prescribed(self, time):
        left, right = time + self.k/2, time - self.k/2
        positions = np.array([radius(left), radius(right), 0., 0.,
                              self.point_at_wall + self.inward_speed*(self.wall-time),
                              self.fraction*self.gap, (self.fraction-1)*self.gap, 0.])
        speeds = np.array([velocity(left), velocity(right), 0., 0., -self.inward_speed,
                           0., 0., 0.])
        return positions, speeds


def prepare(j, wall, fraction=None):
    k = 1/np.sqrt(j*(j+1))
    mass = .6
    gap = np.hypot(mass, k)
    delta = radius(wall+k/2) - radius(wall-k/2)
    frequency = np.sqrt(gap**2+j*(j+1)*delta**2)
    if fraction is None:
        fraction = (frequency+gap)/(2*(j+1)*gap)
    speed = j*(.25 if wall == END else .4)
    return Preparation(j, wall, k, mass, fraction, -j*radius(wall+k/2), speed)


def geometry(config, positions):
    w_l, w_r, center_l, center_r, point, r_l, r_r, r_p = positions
    delta = w_l-w_r
    omega_sq = ((r_l-r_r)**2+(center_l-center_r)**2
                + config.j*(config.j+1)*delta**2)
    axial = np.array([config.j*w_l+point-center_l, config.j*w_r+point-center_r])
    transverse = np.array([r_l-r_p, r_r-r_p])
    return omega_sq, axial, transverse


def spin_reading(config):
    coordinates, speeds = config.prescribed(config.wall)
    freq_sq, axial, transverse = geometry(config, coordinates)
    energies = np.hypot(axial, transverse)
    spinors = [np.linalg.eigh(z*SZ+x*SX)[1] for z, x in zip(axial, transverse)]
    matrix_element = float(abs(np.vdot(spinors[0][:, 1], SY@spinors[1][:, 0]))**2)
    dot = np.prod(axial) + np.prod(transverse)
    weight = (1+dot/np.prod(energies))/2
    diff_sq = (axial[0]-axial[1])**2 + (transverse[0]-transverse[1])**2
    excess = config.j*(coordinates[0]-coordinates[1])**2
    np.testing.assert_allclose([weight, freq_sq-diff_sq, energies.sum()**2-diff_sq],
                               [matrix_element, excess, 4*np.prod(energies)*weight], atol=3e-13)
    if abs(energies.sum()-np.sqrt(freq_sq)) < 1e-10:
        np.testing.assert_allclose(matrix_element, excess/(4*np.prod(energies)), atol=3e-13)
    times = np.linspace(0, config.wall, 240)
    prewall = [config.prescribed(time)[0] for time in times[:-1]]
    min_left = min(p[4]-config.j*abs(p[0]) for p in prewall)
    min_right = min(p[4]-config.j*abs(p[1]) for p in prewall)
    assert min_left>0 and min_right>0 and coordinates[0]<0
    return dict(j=config.j, clock=config.wall, gap=config.gap, fraction=config.fraction,
                wall_slope=config.j*speeds[0]+speeds[4], right_axial=axial[1],
                frequency=np.sqrt(freq_sq), left_energy=energies[0], right_energy=energies[1],
                mismatch=energies.sum()-np.sqrt(freq_sq), spin_weight=matrix_element,
                casimir_excess=excess,one_boson_vertex_per_g_squared=matrix_element/(2*(2*config.j+1)*np.sqrt(freq_sq)))


def colour_check(config):
    j = config.j
    matrices = spin_matrices(j)
    n = 2*j+1
    pos, _ = config.prescribed(config.wall)
    omega_sq, axial, _ = geometry(config, pos)
    identity = np.eye(n)
    force = np.zeros((n,n), dtype=complex)
    for i, generator in enumerate(matrices):
        left = pos[0]*generator + (pos[2] if i==2 else 0)*identity
        right = pos[1]*generator + (pos[3] if i==2 else 0)*identity
        first = left-right
        force += left@first-first@right
    np.testing.assert_allclose(force+(pos[5]-pos[6])**2*identity, omega_sq*identity, atol=1e-11)
    down = np.zeros(2*n)
    down[n+np.argmin(np.diag(matrices[2]).real)] = 1.
    indices = []
    for w, center, expected in zip(pos[:2],pos[2:4],axial):
        localizer = (w*sum(np.kron(p,mat) for p,mat in zip((SX,SY,SZ),matrices))
                     + (center-pos[4])*np.kron(SZ,identity))
        np.testing.assert_allclose(localizer@down, expected*down, atol=3e-12)
        indices.append(float(sorted(abs(np.linalg.eigvalsh(localizer)))[1]))
    assert min(indices)>0.1
    return dict(j=j, next_level_abs=indices, colour_degeneracy=n)


def wedge(one_body):
    """Second quantization on the two-fermion wedge of four end orbitals."""
    result = np.zeros((6,6), dtype=complex)
    for source, mask in enumerate(MASKS):
        for old in range(4):
            if not mask & (1<<old):
                continue
            intermediate = mask ^ (1<<old)
            for new in range(4):
                if intermediate & (1<<new):
                    continue
                target = MASKS.index(intermediate | (1<<new))
                swaps = (mask % (1<<old)).bit_count() + (intermediate % (1<<new)).bit_count()
                result[target,source] += (-1)**swaps * one_body[new,old]
    return result


def collective(local, counts, index):
    """Permutation-symmetric sum of the same even bilinear over spin copies."""
    result = np.zeros((len(counts),len(counts)), dtype=complex)
    rows, cols = np.nonzero(local)
    for col, numbers in enumerate(counts):
        for new, old in zip(rows,cols):
            if numbers[old]==0:
                continue
            out = list(numbers)
            out[old] -= 1
            factor = np.sqrt(numbers[old]*(out[new]+1))
            out[new] += 1
            result[index[tuple(out)],col] += factor*local[new,old]
    return result


def sparse(entries, shape):
    if not entries:
        return coo_matrix(shape,dtype=complex).tocsr()
    rows, cols, values = zip(*entries)
    return coo_matrix((values,(rows,cols)),shape=shape).tocsr()


class Endpoints:
    def __init__(self, copies, cutoff):
        self.copies = copies
        self.cutoff = cutoff
        counts = [tuple(record.count(a) for a in range(6))
                  for record in combinations_with_replacement(range(6),copies)]
        self.counts = counts
        index = {entry:i for i,entry in enumerate(counts)}
        charge_one = np.array([(mask & 3).bit_count()-1 for mask in MASKS])
        charges = np.asarray(counts)@charge_one
        states = [(c, level+max(0,-q), level+max(0,q))
                  for c,q in enumerate(charges) for level in range(cutoff+1)]
        lookup = {state:i for i,state in enumerate(states)}
        self.states = states
        self.charge = np.array([charges[c] for c,_,_ in states])
        self.na = np.array([a for _,a,_ in states])
        self.nb = np.array([b for _,_,b in states])
        assert np.all(self.charge+self.na-self.nb==0)
        self.number = self.na+self.nb+1
        size = len(states)
        matrices = []
        for side in (0,1):
            for spin in (SZ,SX):
                one_body = np.zeros((4,4),dtype=complex)
                one_body[2*side:2*side+2,2*side:2*side+2] = spin
                matrices.append(collective(wedge(one_body),counts,index))
        one_body = np.zeros((4,4),dtype=complex)
        one_body[:2,2:] = SY
        hop = collective(wedge(one_body),counts,index)
        diagonal = [matrices[a].diagonal().real for a in (0,2)]
        self.z = np.array([v[[c for c,_,_ in states]] for v in diagonal])
        other = [[] for _ in range(4)]
        boundary = [[],[]]
        outside = {(c,cutoff+1+max(0,-q),cutoff+1+max(0,q)):c for c,q in enumerate(charges)}
        for col,(c,a,b) in enumerate(states):
            for i,mat in enumerate((matrices[1],matrices[3])):
                for r in np.flatnonzero(mat[:,c]):
                    other[i].append((lookup[(r,a,b)],col,mat[r,c]))
            for da,db,coeff in ((1,1,np.sqrt((a+1)*(b+1))),(-1,-1,np.sqrt(a*b))):
                if not coeff:
                    continue
                key = (c,a+da,b+db)
                if key in lookup:
                    other[2].append((lookup[key],col,coeff))
                else:
                    boundary[0].append((outside[key],col,coeff))
            for op, steps in ((hop,((-1,0,np.sqrt(a)),(0,1,np.sqrt(b+1)))),
                              (hop.conj().T,((1,0,np.sqrt(a+1)),(0,-1,np.sqrt(b))))):
                for r in np.flatnonzero(op[:,c]):
                    for da,db,coeff in steps:
                        if not coeff:
                            continue
                        key=(r,a+da,b+db)
                        item=(col,coeff*op[r,c])
                        if key in lookup:
                            other[3].append((lookup[key],*item))
                        else:
                            boundary[1].append((outside[key],*item))
        self.xl,self.xr,self.squeeze,self.hop = [sparse(entry,(size,size)) for entry in other]
        self.boundary = [sparse(entry,(len(counts),size)) for entry in boundary]
        for mat in (self.xl,self.xr,self.squeeze,self.hop):
            err=mat-mat.getH()
            assert not err.nnz or np.max(abs(err.data))<4e-14

    def vacuum(self, axial, transverse):
        vec = [np.linalg.eigh(z*SZ+x*SX)[1][:,0] for z,x in zip(axial,transverse)]
        orbital = np.zeros((4,2),dtype=complex)
        orbital[:2,0],orbital[2:,1]=vec
        single=[np.linalg.det(orbital[[i for i in range(4) if mask&(1<<i)],:]) for mask in MASKS]
        amplitudes = np.array([np.sqrt(factorial(self.copies)/prod(factorial(i) for i in row))
                               *prod(v**n for v,n in zip(single,row)) for row in self.counts])
        result=np.array([amplitudes[c] if a==b==0 else 0j for c,a,b in self.states])
        np.testing.assert_allclose(np.linalg.norm(result),1.,atol=1e-12)
        return result


def advance(config, basis, coupling_sq=.04, recoil=False, monitor_yukawa=True):
    """Evolve the joint link and filled endpoints and optionally vary the collective coordinates."""
    j, gap = config.j, config.gap
    inertia = (2*j+1)*j*(j+1)/coupling_sq
    mass = np.array([inertia,inertia,(2*j+1)/coupling_sq,(2*j+1)/coupling_sq,
                     1/coupling_sq,(2*j+1)/coupling_sq,(2*j+1)/coupling_sq,1/coupling_sq])
    yukawa = np.sqrt(coupling_sq/(2*(2*j+1)*gap)) if monitor_yukawa else 0.
    position, speed = config.prescribed(0.)
    freq_sq, axial, transverse = geometry(config, position)
    np.testing.assert_allclose(freq_sq,gap**2,atol=3e-14)
    initial = basis.vacuum(axial,transverse)
    size = initial.size
    y0 = np.r_[initial,position,speed,0.,0.]

    def physical(time,state):
        if recoil:
            return state[size:size+8].real, state[size+8:size+16].real
        return config.prescribed(time)

    def kinetic(time,state):
        coordinates,speeds=physical(time,state)
        psi=state[:size]
        frequency_sq,axial,perpendicular=geometry(config,coordinates)
        squeeze=(frequency_sq-gap**2)/(2*gap)
        square_q=basis.number*psi + basis.squeeze@psi
        x_l,x_r,hop=basis.xl@psi,basis.xr@psi,basis.hop@psi
        hpsi=((gap*basis.number+axial[0]*basis.z[0]+axial[1]*basis.z[1])*psi
              +squeeze*square_q+perpendicular[0]*x_l+perpendicular[1]*x_r+yukawa*hop)
        modulus=abs(psi)**2
        norm=modulus.sum()
        z_l,z_r=basis.z@modulus/norm
        left_x,right_x=[np.vdot(psi,v).real/norm for v in (x_l,x_r)]
        size_q=np.vdot(psi,square_q).real/(gap*norm)
        w_l,w_r,c_l,c_r,_,r_l,r_r,_=coordinates
        radial_force=j*(j+1)*(w_l-w_r)*size_q
        center_force=(c_l-c_r)*size_q
        transverse_force=(r_l-r_r)*size_q
        gradient=np.array([radial_force+j*z_l, -radial_force+j*z_r,
                           center_force-z_l, -center_force-z_r, z_l+z_r,
                           transverse_force+left_x, -transverse_force+right_x, -left_x-right_x])
        energy=np.vdot(psi,hpsi).real/norm
        return hpsi,energy,gradient,squeeze,yukawa*np.vdot(psi,hop).real/norm

    def rhs(time,state):
        coordinates,speeds=physical(time,state)
        psi=state[:size]
        hpsi,en,gradient,pump,_=kinetic(time,state)
        # Removing a common phase improves convergence and has no effect on the forces.
        dpsi=-1j*(hpsi-en*psi)
        accel=-gradient/mass
        accel[:2]-=2*coordinates[:2]**3
        flux=np.linalg.norm(pump*(basis.boundary[0]@psi)+yukawa*(basis.boundary[1]@psi))
        return np.r_[dpsi,speeds if recoil else np.zeros(8),accel if recoil else np.zeros(8),
                     gradient@speeds,flux]

    def wall(time,state):
        pos,_=physical(time,state)
        return j*pos[0]+pos[4]-pos[2]
    wall.direction=-1
    wall.terminal=True
    stop=config.wall+.12 if recoil else config.wall
    sol=solve_ivp(rhs,(0.,stop),y0,method="DOP853",rtol=1.5e-9,atol=2.0e-12,
                  events=wall if recoil else None,dense_output=True)
    assert sol.success
    if recoil:
        assert len(sol.t_events[0])==1, "The first inward crossing was not located."
    final=sol.y[:,-1]
    hit=sol.t[-1]
    pos,vel=physical(hit,final)
    p=abs(final[:size])**2
    norm=float(p.sum())
    assert abs(norm-1)<2e-8
    p/=norm
    probabilities=[float(p[basis.charge==u].sum()) for u in range(-basis.copies,basis.copies+1)]
    np.testing.assert_allclose(probabilities,probabilities[::-1],atol=4e-9)
    field_pair=float(p[np.minimum(basis.na,basis.nb)>0].sum())
    common_work=float(final[-2].real)
    h0=kinetic(0.,y0)[1]
    _,h1,_,_,int_energy=kinetic(hit,final)
    error=abs(h1-h0-common_work)
    assert error<1.5e-6
    def background_energy(y,v):
        return (mass@(v*v)+inertia*sum(y[:2]**4))/2
    def conserved_center(v):
        return [mass[2:5]@v[2:5],mass[5:]@v[5:]]
    max_balance=0.
    min_margin=None
    for t,st in zip(np.linspace(0,hit,17),sol.sol(np.linspace(0,hit,17)).T):
        y,v=physical(t,st)
        eq=kinetic(t,st)[1]
        max_balance=max(max_balance,abs(eq-h0-st[-2].real))
        if recoil:
            err=eq+background_energy(y,v)-h0-background_energy(position,speed)
            assert abs(err)<7e-6
            np.testing.assert_allclose(conserved_center(v),conserved_center(speed),atol=1e-8)
        if t<hit:
            margin= y[4]-y[2]-abs(j*y[0])
            min_margin=margin if min_margin is None else min(min_margin,margin)
    assert min_margin>0
    ptrace=float(sum(probabilities[:basis.copies])+sum(probabilities[basis.copies+1:]))
    return dict(j=j,clock_target=config.wall,k=config.k,fraction=config.fraction,
                copies=basis.copies,pair_cutoff=basis.cutoff,g1_squared=coupling_sq,
                recoil=recoil,yukawa_active=monitor_yukawa,clock_at_wall=float(hit),
                charge_probabilities=probabilities,charged=ptrace,
                paired_in_reference_basis=field_pair,mean_reference_bosons=float((basis.number-1)@p),
                quantum_energy_change=h1-h0,work=common_work,
                collective_energy_change=background_energy(pos,vel)-background_energy(position,speed),
                charge_dephasing_energy_defect=-int_energy,
                norm_error=abs(norm-1),max_work_error=max_balance,
                integrated_omitted_amplitude=float(final[-1].real),
                highest_pair_shell=float(sum(p[np.minimum(basis.na,basis.nb)==basis.cutoff])),
                residual_axial=float(wall(hit,final)),right_axial=float(j*pos[1]+pos[4]-pos[3]))


def local_conjugation():
    """Unitary particle-hole transformation in the two-fermion wedge."""
    matrix=np.zeros((6,6),complex)
    for col,occupied in enumerate(MASKS):
        filled=15
        amplitude=1
        for i in reversed([i for i in range(4) if occupied&(1<<i)]):
            partner=i^1
            amplitude*=(-1)**((filled%(1<<partner)).bit_count() + (i%2))
            filled^=(1<<partner)
        matrix[MASKS.index(filled),col]=amplitude
    return matrix


def readout_checks(basis,config,g2):
    single_c=local_conjugation()
    one=np.zeros((4,4),complex)
    one[:2,2:]=SY
    rising=wedge(one)
    grade=np.diag([(mask&3).bit_count()-1 for mask in MASKS])
    np.testing.assert_allclose(rising@rising.conj().T-rising.conj().T@rising,2*grade)
    for spin in (SZ,SX):
        for side in (0,1):
            one=np.zeros((4,4),complex)
            one[2*side:2*side+2,2*side:2*side+2]=spin
            onsite=wedge(one)
            np.testing.assert_allclose(single_c@onsite@single_c.conj().T,onsite)
    np.testing.assert_allclose(single_c@rising@single_c.conj().T,rising.conj().T)
    np.testing.assert_allclose(single_c@grade@single_c.conj().T,-grade)
    # Test exact continuum identities on vectors of finite support, away from the cutoff.
    tests=[]
    M=config.gap
    scale_sq=g2/(2*(2*config.j+1)*M)
    omega_sq=geometry(config,config.prescribed(config.wall)[0])[0]
    for charge in range(1,basis.copies+1):
        ids=np.flatnonzero((basis.charge==charge)&(np.minimum(basis.na,basis.nb)<=3))
        psi=np.zeros(len(basis.states),complex)
        psi[ids]=(np.cos(ids*.81)+1j*np.sin(ids*.39))/(1+np.minimum(basis.na[ids],basis.nb[ids]))
        psi/=np.linalg.norm(psi)
        squeeze=np.vdot(psi,basis.squeeze@psi).real
        occupation=(abs(psi)**2)@basis.number
        radius_sq=(occupation+squeeze)/M
        momentum_sq=M*(occupation-squeeze)
        oscillator_energy=(momentum_sq+omega_sq*radius_sq)/2
        outgoing=(basis.hop@psi)*np.sqrt(scale_sq)
        assert np.linalg.norm(outgoing[basis.charge==charge])<1e-12
        leakage=float(np.linalg.norm(outgoing)**2)
        direct=g2*charge*radius_sq/(2*config.j+1)
        floor=g2*charge*(charge+1)**2/(2*(2*config.j+1)*oscillator_energy)
        assert radius_sq*momentum_sq>=(charge+1)**2-1e-12
        assert leakage>=direct-1e-12 and direct>=floor-1e-12
        tests.append(dict(q=charge,radius_squared=radius_sq,energy=oscillator_energy,
                          outward_norm_squared=leakage,coordinate_bound=direct,energy_bound=floor))
    return tests


def screened_matter(cutoff=13):
    """One resolved doublet, opposite membrane profiles and a free axial point."""
    basis=Endpoints(1,cutoff)
    one=np.zeros((4,4),complex)
    one[:2,2:]=SY
    raising=wedge(one)
    spectrum,vec=np.linalg.eigh(raising@raising.conj().T+raising.conj().T@raising)
    dark=vec[:,abs(spectrum)<1e-10]
    assert dark.shape==(6,3)
    spin_projection=dark@dark.conj().T
    # The oscillator link can be exactly empty with one fermion remaining at each end.
    spin_ids=[row.index(1) for row in basis.counts]
    q= np.array([(mask&3).bit_count()-1 for mask in MASKS])
    np.testing.assert_allclose(np.diag(q)@spin_projection,0.,atol=1e-12)
    def project(psi):
        result=np.zeros_like(psi)
        for h in range(basis.cutoff+1):
            ids=np.flatnonzero((basis.na==h)&(basis.nb==h))
            orbitals=[spin_ids[basis.states[i][0]] for i in ids]
            result[ids]=spin_projection[np.ix_(orbitals,orbitals)]@psi[ids]
        return result
    j,g2,mass,amplitude=2,.32,.6,.35
    start=-1.4
    def w(time):
        return amplitude*radius(amplitude*time)
    def frequency(t):
        return np.hypot(mass,2*np.sqrt(j*(j+1))*w(t))
    ref=frequency(start)
    strength=np.sqrt(g2/(2*(2*j+1)*ref))
    def initial(sign):
        psi=np.zeros(len(basis.states),complex)
        idx=np.flatnonzero((basis.charge==sign)&(np.minimum(basis.na,basis.nb)==0))
        assert len(idx)==1
        psi[idx[0]]=1.
        return psi
    def spin_in_vacuum(time,psi):
        omega=frequency(time)
        coef=2*np.sqrt(omega*ref)/(omega+ref)
        ratio=(ref-omega)/(ref+omega)
        spin=np.zeros(6,complex)
        for i,(c,a,b) in enumerate(basis.states):
            if a==b:
                spin[spin_ids[c]]+=coef*ratio**a*psi[i]
        return spin_projection@spin
    def evolve(t0,t1,psi,speed):
        def rhs(t,st):
            axial=j*w(t)
            z=(axial+speed*t)*basis.z[0]+(-axial+speed*t)*basis.z[1]
            squeeze=(frequency(t)**2-ref**2)/(2*ref)
            return -1j*((ref*basis.number+z)*st+squeeze*(basis.number*st+basis.squeeze@st)
                         +(mass/2)*(basis.xl@st-basis.xr@st)+strength*(basis.hop@st))
        sol=solve_ivp(rhs,(t0,t1),psi,method="DOP853",rtol=2e-12,atol=2e-14,dense_output=True)
        assert sol.success and abs(np.linalg.norm(sol.y[:,-1])-1)<1e-10
        return sol.sol
    speed=.35
    plus,minus=[evolve(start,0.,initial(s),speed) for s in (1,-1)]
    final,other=spin_in_vacuum(0.,plus(0.)),spin_in_vacuum(0.,minus(0.))
    probability=np.linalg.norm(final)**2
    fidelity=abs(np.vdot(final,other))**2/(probability*np.linalg.norm(other)**2)
    np.testing.assert_allclose(fidelity,1.,atol=2e-12)
    coeff=g2*(2*speed*start)**2/(4*(2*j+1)*ref)
    ratios=[np.linalg.norm(spin_in_vacuum(start+dt,plus(start+dt)))**2/(coeff*dt**4)
            for dt in (.04,.02,.01,.005,.0025,.00125)]
    assert all(abs(new-1)<abs(old-1) for old,new in zip(ratios,ratios[1:]))
    assert abs(ratios[-1]-1)<.002 and probability>.0001
    v0=project(plus(0.))
    v0/=np.linalg.norm(v0)
    record=evolve(0.,.65,v0,speed)(.65)
    survival=float(np.linalg.norm(project(record))**2)
    assert 1-survival<=speed**2*.65**4+1e-10
    fixed=evolve(0.,1.,v0,0.)(1.)
    np.testing.assert_allclose(np.linalg.norm(project(fixed)),1.,atol=2e-11)
    never_loaded=spin_in_vacuum(0.,evolve(start,0.,initial(1),0.)(0.))
    assert np.linalg.norm(never_loaded)<2e-12
    return dict(spin_dimension=3,speed=speed,clock_start=start,j=j,g1_squared=g2,
                point_mass_separation=mass,radial_amplitude=amplitude,
                prepared_frequency=ref,short_time_coefficient=coeff,short_time_ratios=ratios,
                neutral_vacuum_probability=float(probability),opposite_sign_fidelity=float(fidelity),
                neutral_survival_at_point65=survival,maximum_loss_bound=speed**2*.65**4,
                protected_norm=float(np.linalg.norm(project(fixed))),matched_loading_norm=float(np.linalg.norm(never_loaded)))


def tidal_information():
    """Reduced outgoing states of the two material axes in the Schwarzschild tidal tube."""
    from cat_core_multiplet import matched_caps,polarized_transfer
    clock,profiles,_,_=matched_caps()
    k=.16
    rotations=[polarized_transfer(clock,profiles,h,k)[0] for h in (0.,.08)]
    vectors=[.5*(r-np.eye(4))[:2,0] for r in rotations]
    probabilities=[float(v@v) for v in vectors]
    determinant=float(vectors[0][0]*vectors[1][1]-vectors[0][1]*vectors[1][0])
    oriented=[determinant**2/p for p in probabilities]
    checks=[]
    for index,v in enumerate(vectors):
        normal=np.array([-v[1],v[0]])/np.sqrt(probabilities[index])
        rho=np.zeros((3,3))
        rho[0,0]=1-probabilities[index]
        rho[1:,1:]=np.outer(v,v)
        probe=np.r_[0.,normal]
        assert np.linalg.norm(rho@probe)<1e-14
        got=abs(normal@vectors[1-index])**2
        np.testing.assert_allclose(got,oriented[index],rtol=8e-9,atol=1e-27)
        checks.append(float(got))
    theta=float(max(abs(np.angle(np.linalg.eigvals(rotations[0].T@rotations[1])))))
    assert min(oriented)>0 and max(oriented)<=np.sin(theta)**2
    return dict(longitudinal_offset=k,material_vectors=[v.tolist() for v in vectors],
                ordinary_nonempty=probabilities,exclusive_other_given_zero_here=checks,
                unrestricted_polarization_ceiling=np.sin(theta)**2,
                equal_prior_unambiguous_ceiling=2*np.sin(theta/2)**2)


def single_transfer(config, coupling_sq=.04, copies=4):
    """Leading Dyson amplitude and an all-orders upper bound with the same input."""
    frequency=config.gap
    _,axial,perp=geometry(config,config.prescribed(0.)[0])
    initial=[np.linalg.eigh(z*SZ+x*SX)[1][:,0] for z,x in zip(axial,perp)]
    # v and its derivative normalize a *complex* matrix coordinate. A single
    # insertion creates one compensating quantum in the interaction picture.
    y0=np.r_[initial[0],initial[1],1/np.sqrt(2*frequency),-1j*np.sqrt(frequency/2),0j,0j]
    def rhs(t,y):
        freq_sq,axial,perp=geometry(config,config.prescribed(t)[0])
        left,right=y[:2],y[2:4]
        spin=SY@right
        determinant=left[0]*spin[1]-left[1]*spin[0]
        term=np.conj(y[4])*determinant
        return np.r_[-1j*(axial[0]*(SZ@left)+perp[0]*(SX@left)),
                     -1j*(axial[1]*(SZ@right)+perp[1]*(SX@right)),
                     y[5],-freq_sq*y[4],term,abs(term)]
    sol=solve_ivp(rhs,(0.,config.wall),y0,method="DOP853",rtol=2e-10,atol=3e-13)
    assert sol.success
    out=sol.y[:,-1]
    birth=2*copies*coupling_sq/(2*config.j+1)
    leading=birth*abs(out[-2])**2
    bound=birth*out[-1].real**2
    assert leading<=bound+1e-12
    return dict(j=config.j,leading_probability=float(leading),duhamel_bound=float(min(1.,bound)),
                coherent_amplitude_integral=abs(out[-2]),absolute_amplitude_integral=out[-1].real)


def run():
    matching = [spin_reading(prepare(j,1.95)) for j in (4,8,32,128,512)]
    dark=[spin_reading(prepare(j,END,.5)) for j in (8,32)]
    off=[spin_reading(prepare(j,1.95,.5)) for j in (8,32,128)]
    assert max(x["spin_weight"] for x in dark)<1e-20
    assert max(abs(x["mismatch"]) for x in matching)<2e-13
    assert all(x["spin_weight"]>.15 for x in matching) and min(x["mismatch"] for x in off)>.01
    geometric=[colour_check(prepare(j,t,frac)) for j,t,frac in ((2,1.95,None),(5,1.95,None),(4,END,.5))]
    active=Endpoints(4,25)
    config=prepare(8,1.95)
    # A second physical matrix preparation sets the longitudinal offset to zero.
    # Its membrane trajectories coincide and its scalar link has constant frequency.
    calibration=Preparation(config.j,config.wall,0.,config.gap,config.fraction,
                            -config.j*radius(config.wall),config.inward_speed)
    no_hop=advance(prepare(8,END,.5),active,monitor_yukawa=False)
    assert no_hop["charged"]<1e-16
    # Independent untruncated harmonic mode, with both real polarizations.
    from cat_timelike_receiver import finite_clock
    real_nonempty=finite_clock(8,0.)["nonempty"]
    np.testing.assert_allclose(no_hop["paired_in_reference_basis"],1-(1-real_nonempty)**2,atol=3e-7)
    fixed=advance(config,active)
    control=advance(calibration,active)
    symmetric=advance(prepare(8,END,.5),active)
    back=advance(config,active,recoil=True)
    assert min(r["charged"] for r in (fixed,control,symmetric,back))>1e-5
    assert min(abs(r["charge_dephasing_energy_defect"]) for r in (fixed,control,symmetric,back))>1e-5
    higher=advance(config,Endpoints(4,38))
    convergence=max(abs(a-b) for a,b in zip(fixed["charge_probabilities"],higher["charge_probabilities"]))
    assert convergence<1e-7
    singlet=advance(config,Endpoints(1,14))
    bounds=[single_transfer(prepare(j,1.95)) for j in (8,32,128)]
    weak=advance(config,Endpoints(4,18),coupling_sq=.0004)
    assert fixed["charged"]<=bounds[0]["duhamel_bound"]
    weak_ratio=weak["charged"]/(bounds[0]["leading_probability"]*.01)
    assert abs(weak_ratio-1)<.003
    screened=screened_matter()
    screened_check=screened_matter(19)
    neutral_error=max(abs(screened[key]-screened_check[key]) for key in
                      ('neutral_vacuum_probability','neutral_survival_at_point65'))
    assert neutral_error<2e-9
    result=dict(resonant_left_wall=matching,simultaneous=dark,midpoint_off_resonance=off,
                full_colour_tests=geometric,frozen_background=[fixed,control,symmetric,no_hop],
                collective_recoil=back,high_cutoff=higher,one_doublet=singlet,
                cutoff_change_in_probabilities=convergence,
                signed_grade_leakage=readout_checks(active,config,.04),screened_channel=screened,
                neutral_cutoff_comparison=neutral_error,schwarzschild_tidal_information=tidal_information(),
                finite_time_bounds=bounds,weak_coupling_check=weak_ratio)
    path=ROOT/"verification/cat-compensated-yukawa-results.json"
    path.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Verified compensated fermion transfer on two membranes and a point.")


if __name__=="__main__":
    run()
