"""Matter on the rotating CAT branch and a quantized weak type-IIA tide (T.14)."""
import json
import argparse
from itertools import product
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigh_tridiagonal
from scipy.special import erfc, ndtr, iv
from scipy.optimize import brentq

from cat_oriented_bounce import ChargedProbe, ODE, START, geometry, spin_matrices


def evolve(rhs, initial):
    solution = solve_ivp(rhs, (START, 0.), initial, **ODE)
    assert solution.success, solution.message
    return solution.sol


def gauss(nodes):
    x, w = np.polynomial.legendre.leggauss(nodes)
    return (1-x)*START/2, -START*w/2


def norm2(array):
    return float(np.vdot(array, array).real)


def edge_count_law(filled, empty, edge, amplitudes):
    """Exterior power of the counting rotation for the filled sea plus one particle."""
    rho = sum(a@a.conj().T for a in amplitudes)
    rho /= np.trace(rho)
    size = edge.shape[1]+1
    generating = []
    vacuum = []
    p, q = edge.conj().T@filled, edge.conj().T@empty
    for z in np.exp(2j*np.pi*np.arange(size)/size):
        vee = np.eye(filled.shape[1])+(z-1)*p.conj().T@p
        wee = np.eye(empty.shape[1])+(z-1)*q.conj().T@q
        crossed = (z-1)**2*q.conj().T@p@np.linalg.solve(vee, p.conj().T@q)
        vacuum.append(np.linalg.det(vee))
        generating.append(vacuum[-1]*np.trace(rho@(wee-crossed)))
    laws = np.fft.fft([generating, vacuum], axis=1)/size
    assert np.max(abs(laws.imag)) < 2e-12 and laws.real.min() > -2e-12
    np.testing.assert_allclose(laws.real.sum(axis=1), 1., atol=2e-12)
    mean_excess = float(np.arange(size)@(laws[0]-laws[1]).real)
    np.testing.assert_allclose(mean_excess, np.trace(q@rho@q.conj().T).real, atol=2e-12)
    return dict(charged_law=laws[0].real.tolist(), sea_law=laws[1].real.tolist(),
                extra_edge_occupation=mean_excess)


class Receiver:
    def __init__(self, j):
        self.probe = p = ChargedProbe(j)
        normal_separation = .6
        scale = 1-.8/np.sqrt(j*(j+1))
        fraction = (1+normal_separation)/(2*(j+1)*normal_separation)
        color = np.eye(p.colors)
        self.orbits = [geometry(j, j, -.25*j, scale=s)[0] for s in (1., scale)]
        ninth = np.diag([(-1)**n.bit_count() for n in range(16)])
        np.testing.assert_allclose([ninth@g+g@ninth for g in p.gamma], 0.)
        self.vertices = [np.kron(g, color) for g in (p.gamma[7], ninth)]
        normal = np.kron(p.gamma[6], color)
        self.spinors = []
        for side, orbit in enumerate(self.orbits):
            def hamiltonian(t, path=orbit, xi=(fraction-side)*normal_separation):
                return p.hamiltonian(path(t))+xi*normal
            levels, frame = np.linalg.eigh(hamiltonian(START))
            assert sum(levels < 0)*2 == len(levels) and min(abs(levels)) > 1e-4
            def rhs(t, y, h=hamiltonian):
                return (-1j*h(t)@y.reshape(frame.shape)).ravel()
            self.spinors.append(evolve(rhs, frame.astype(complex).ravel()))

        def frequency2(t):
            delta = self.orbits[0](t)[:2]-self.orbits[1](t)[:2]
            return normal_separation**2+j*(j+1)*np.dot(delta, delta)
        w = np.sqrt(frequency2(START))
        self.mode = evolve(lambda t, y: [y[1], -frequency2(t)*y[0]],
                           [1/np.sqrt(2*w), -1j*np.sqrt(w/2)])
        self.mass = (2*p.colors+1)*1.e9

    def frames(self, t):
        return [np.split(sol(t).reshape((self.probe.size,)*2), 2, axis=1)
                for sol in self.spinors]

    def amplitudes(self, k, nodes):
        def phase(t):
            recoil = k*k/(2*self.mass)
            return np.exp(1j*np.array([-k+recoil, k+recoil])*t)
        def integrands(t, _):
            v = self.mode(t)[0]
            return np.r_[phase(t)*v.conjugate()**2, phase(t)*abs(v)**2]
        primitives = evolve(integrands, np.zeros(4, dtype=complex))
        total = primitives(0.)
        half = self.probe.size//2
        # Axes are fate of the wave (absorb/emit/absent), charge sign,
        # ordinary polarization, extra particle and missing particle.
        amplitudes = np.zeros((3, 2, 2, half, half), dtype=complex)
        times, weights = gauss(nodes)
        for t, weight in zip(times, weights):
            v = self.mode(t)[0]
            before, partial = np.split(primitives(t), 2)
            ordered = v*before+v.conjugate()*(total[2:]-partial)
            (lf, le), (rf, re) = self.frames(t)
            for a, vertex in enumerate(self.vertices):
                factors = weight*np.r_[(1-2*a)*ordered, v.conjugate()]/np.sqrt(self.probe.colors)
                current = np.array([le.conj().T@vertex@rf, re.conj().T@vertex@lf])
                amplitudes[:, :, a] += factors[:, None, None, None]*current[None]
        return amplitudes, total[:2]

    def measure(self, k, nodes):
        amp, make_pair = self.amplitudes(k, nodes)
        weight = np.sum(abs(amp)**2, axis=(2, 3, 4))
        np.testing.assert_allclose(weight[:, 0], weight[:, 1], rtol=2e-11)
        def overlap(first, second):
            return norm2(np.vdot(first, second))/(norm2(first)*norm2(second))
        overlaps = [overlap(amp[i, 0], amp[2, 0]) for i in (0, 1)]
        assert max(overlaps) < 1e-23
        assert norm2(np.vdot(amp[0, 0, 0], amp[2, 0, 0])) > 1e-9
        edge = self.probe.edge(self.orbits[0](0.))
        filled, empty = self.frames(0.)[0]
        return dict(angular_frequency=k, left_charge_weights=weight[:, 0].tolist(),
                    right_charge_weights=weight[:, 1].tolist(),
                    three_link_left_charge_weights=(3*abs(make_pair)**2*weight[2, 0]).tolist(),
                    ordinary_overlaps_squared=overlaps,
                    absorb_emit_internal_overlap_squared=overlap(amp[0, 0], amp[1, 0]),
                    north_edge_if_absorbed=edge_count_law(filled, empty, edge, amp[0, 0]))


def fock_ordering_test():
    """Act on four occupation numbers directly, independently of Wick contraction."""
    vacuum = (0, 0, 0, 0)
    def ladder(state, i, create):
        out = {}
        for key, amplitude in state.items():
            n = key[i]
            if n or create:
                new = list(key)
                new[i] += 1 if create else -1
                out[tuple(new)] = amplitude*np.sqrt(n+int(create))
        return out
    def add(out, term, coeff):
        for key, val in term.items():
            out[key] = out.get(key, 0.)+coeff*val
    def z(state, a, v, adjoint=False):
        out = {}
        add(out, ladder(state, 2*a+int(adjoint), False), v)
        add(out, ladder(state, 2*a+int(not adjoint), True), v.conjugate())
        return out
    def tide(state, w):
        out = {}
        for a in range(2):
            add(out, z(z(state, a, w), a, w, True), 1-2*a)
        return out
    w, v = .52+.37j, .71-.33j
    err = []
    for b in range(2):
        key = tuple(int(i==2*b+1) for i in range(4))
        earlier = z(tide({vacuum: 1.}, w), b, v)
        later = tide(z({vacuum: 1.}, b, v), w)
        err.extend([abs(earlier[key]-(1-2*b)*v*w.conjugate()**2),
                    abs(later[key]-(1-2*b)*v.conjugate()*abs(w)**2)])
        for a in range(2):
            triplet = list(key)
            triplet[2*a] += 1
            triplet[2*a+1] += 1
            expected = (1-2*a)*np.sqrt(1+int(a==b))*v.conjugate()*w.conjugate()**2
            err += [abs(state[tuple(triplet)]-expected) for state in (earlier, later)]
    assert max(err) < 2e-15
    return max(err)


def stationary_and_source():
    # One physical spin transition, two polarizations, all neutral Fock states
    # with at most two ordinary bosons; only occupations 0,1,2 enter at this order.
    m, gap = np.sqrt(2.), 2.
    basis = [(n, e) for n in product(range(3), repeat=4) for e in (0, 1)
             if sum(n)<=2 and n[1]+n[3]-n[0]-n[2]==e]
    levels = np.array([m*sum(n)+gap*e for n, e in basis])
    current = np.zeros((len(basis), len(basis)))
    tide = np.zeros_like(current)
    for i, (n, e) in enumerate(basis):
        tide[i, i] = (n[0]+n[1]-n[2]-n[3])/(2*m)
        for a in range(2):
            new = list(n)
            new[2*a] += 1
            new[2*a+1] += 1
            if (tuple(new), e) in basis:
                l = basis.index((tuple(new), e))
                tide[l, i] = tide[i, l] = (1-2*a)*np.sqrt((n[2*a]+1)*(n[2*a+1]+1))/(2*m)
        if e == 0:
            for index, delta in ((0, -1), (1, 1)):
                new = list(n)
                new[index] += delta
                if (tuple(new), 1) in basis:
                    l = basis.index((tuple(new), 1))
                    current[l, i] = current[i, l] = np.sqrt(n[index]+int(delta==1))/np.sqrt(2*m)
    zero = basis.index(((0, 0, 0, 0), 0))
    final = basis.index(((0, 1, 0, 0), 1))
    # Opposite polarization of the final state is degenerate but exactly decoupled.
    block = [i for i,(n,e) in enumerate(basis) if n[2]==n[3]]
    def matrix_element(g):
        _, v = np.linalg.eigh((np.diag(levels)+g*current)[np.ix_(block, block)])
        def pick(i):
            row = v[block.index(i)]
            a = np.argmax(abs(row))
            return v[:, a]*np.sign(row[a])
        return pick(final)@tide[np.ix_(block, block)]@pick(zero)
    step = 2e-5
    derivative = (matrix_element(step)-matrix_element(-step))/(2*step)
    expected = 1/(np.sqrt(2*m)*(gap**2-m*m))
    np.testing.assert_allclose(derivative, expected, rtol=4e-8)
    spin = ChargedProbe(.5).gamma
    identity = np.eye(16)
    angle_factor = np.trace((identity+spin[0])@spin[7]@(identity-spin[2])@spin[7]).real/4
    np.testing.assert_allclose(angle_factor, 4.)
    mr, ms = 3e9, 2e9
    line = 2*(gap+m)/(1+np.sqrt(1-2*(gap+m)/mr))
    source_gap = line+line**2/(2*ms)
    np.testing.assert_allclose(line-line**2/(2*mr), gap+m, atol=1e-14)
    return dict(dressed_matrix_element_slope=float(derivative), analytic_slope=float(expected),
                each_polarization_spin_summed_weight=float(angle_factor*expected**2),
                matched_line=float(line), source_link_frequency=float(source_gap/2),
                source_antisymmetric_quadrupole_squared=float(2/source_gap**2),
                receiver_recoil=line**2/(2*mr), source_recoil=line**2/(2*ms),
                near_given_one_of_two_in_nine_spatial_dimensions=256/257,
                near_given_one_of_two_in_three_spatial_dimensions=4/5)


def collective_emitter(points):
    # Reduced radial waves use the flat measure dx after multiplication by sqrt(x).
    dx = 8/(points+1)
    x = np.arange(1, points+1)*dx
    def ground(m):
        diag = 1/dx**2+(m*m-.25)/(2*x**2)+x**4/2
        val, vec = eigh_tridiagonal(diag, np.full(points-1, -.5/dx**2),
                                   select="i", select_range=(0, 0))
        return val[0], vec[:, 0]
    lo, v = ground(2)
    hi, w = ground(4)
    return dict(scaled_energy_release=float(hi-lo),
                scaled_quadrupole=float(abs((x*x*v)@w)/12))


def shear(k):
    j = 1.
    orbit = geometry(j, j, -.25*j)[0]
    def rhs(t, y):
        v, dv = y.reshape(2, 2, 2)
        u = orbit(t)[:2]
        hessian = 2*((u@u)*np.eye(2)-np.outer(u, u))
        return np.array([dv, -hessian@v]).ravel()
    unit = np.eye(2)/np.sqrt(2)
    modes = evolve(rhs, np.array([unit, -1j*unit]).ravel())
    times, weights = gauss(52)
    v, dv = modes(0.).reshape(2, 2, 2)
    np.testing.assert_allclose(v@dv.conj().T-v.conj()@dv.T, 1j*np.eye(2), atol=2e-12)
    line = k-k*k/(2*3.e9)
    exc = sum(w*np.exp(-1j*line*t)*orbit(t)[0]*modes(t).reshape(2, 2, 2)[0, 0].conj()
              for t, w in zip(times, weights))
    rho = abs(v[0]@exc)**2/(norm2(v[0])*norm2(exc))
    delta = rho*np.sqrt(2/np.pi)*np.exp(-.5)
    # Independent integration of the folded marginal after absorption.
    integrated = 2*quad(lambda z: (1-rho+rho*z*z)*np.exp(-z*z/2)/np.sqrt(2*np.pi),
                        1, np.inf)[0]
    np.testing.assert_allclose(integrated, erfc(1/np.sqrt(2))+delta, atol=1e-12)
    return dict(angular_frequency=k, excitation_weight_per_eta2_inertia=norm2(exc),
                times_inertia_vacuum_shape_variance=norm2(v[0]), measured_mode_fraction=float(rho),
                relative_shear_variance=float(1+2*rho), negative_gap_vacuum=float(erfc(1/np.sqrt(2))),
                negative_gap_absorbed=float(integrated), optimal_difference=float(delta))


def axial_blocks(j, nodes):
    """All spin and color states, split by the conserved third angular momentum."""
    spin = spin_matrices(j)
    probe = ChargedProbe(.5)
    gs = probe.gamma+[np.diag([(-1)**n.bit_count() for n in range(16)])]
    charges, basis = np.linalg.eigh(-.5j*(gs[0]@gs[1]+gs[3]@gs[4]))
    np.testing.assert_allclose(charges,np.round(charges),atol=1e-13)
    charges = np.rint(charges).astype(int)
    gs = [basis.conj().T@g@basis for g in gs]
    color_count = round(2*j+1)
    block_count = color_count+2
    first, second, offset, normal, p8, p9 = np.zeros((6,block_count,16,16),dtype=complex)
    dims = []
    for b in range(block_count):
        spin_idx = np.where((b-1-charges>=0)&(b-1-charges<color_count))[0]
        color_idx = b-1-charges[spin_idx]
        sp = np.ix_(spin_idx,spin_idx)
        col = np.ix_(color_idx,color_idx)
        same = color_idx[:,None]==color_idx
        n = len(spin_idx)
        dims.append(n)
        for off, mat in ((0,first),(3,second)):
            mat[b,:n,:n] = sum(gs[off+i][sp]*spin[i][col] for i in range(3))
        for g, mat in [(gs[2],offset),(gs[6],normal),(gs[7],p8),(gs[8],p9)]:
            mat[b,:n,:n] = g[sp]*same
    assert sum(dims)==16*color_count
    scale = 1-.8/np.sqrt(j*(j+1))
    xi = .8/(j+1)
    orbits = [geometry(j,j,-j/4,scale=s)[0] for s in (1.,scale)]
    def hamiltonian(t):
        left, right = (f(t) for f in orbits)
        return np.array([v[0]*first+v[1]*second-v[4]*offset+mass*normal
                         for v, mass in ((left,xi),(right,xi-.6))])
    h0 = hamiltonian(START)
    frame = np.zeros_like(h0)
    for side in range(2):
        for b,n in enumerate(dims):
            levels, orbitals = np.linalg.eigh(h0[side,b,:n,:n])
            half = n//2
            assert levels[half-1]<0<levels[half]
            frame[side,b,:n,:half] = orbitals[:,:half]
            frame[side,b,:n,8:8+half] = orbitals[:,half:]
    def rhs(t,y):
        return (-1j*hamiltonian(t)@y.reshape(frame.shape)).ravel()
    times, weights = gauss(nodes)
    settings = {**ODE, "dense_output":False}
    sol = solve_ivp(rhs,(START,0.),frame.ravel(),t_eval=times,**settings)
    assert sol.success
    def frequency2(t):
        du = orbits[0](t)[:2]-orbits[1](t)[:2]
        return .36+j*(j+1)*(du@du)
    omega = np.sqrt(frequency2(START))
    link = evolve(lambda t,y:[y[1],-frequency2(t)*y[0]],
                  [1/np.sqrt(2*omega),-1j*np.sqrt(omega/2)])
    # Keep all open-string energies small as j grows. g1 stays fixed.
    total_mass = (4*j+3)*1e9*j**4
    freq = 4.-8/total_mass
    def integrals(t,y):
        v = link(t)[0]
        return np.exp(-1j*freq*t)*np.array([v.conjugate()**2,abs(v)**2])
    sums = evolve(integrals,np.zeros(2,dtype=complex))
    end = sums(0.)[1]
    amplitude = np.zeros((2,block_count,8,8),dtype=complex)
    for i,(t,w) in enumerate(zip(times,weights)):
        left,right = sol.y[:,i].reshape(frame.shape)
        v = link(t)[0]
        a,b = sums(t)
        factor = w*(v*a+v.conjugate()*(end-b))/np.sqrt(color_count)
        for pol,vertex in enumerate((p8,p9)):
            amplitude[pol] += (1-2*pol)*factor*(left[:,:,8:].conj().swapaxes(1,2)@vertex@right[:,:,:8])
    return dict(spin=j, matrix_colors=color_count, left_absorbed_coefficient=norm2(amplitude),
                highest_axial_block_coefficient=norm2(amplitude[:,-1]), quadrature_nodes=nodes)


def north_spectrum():
    rows = []
    pauli = [2*x for x in spin_matrices(.5)]
    # The increasing magnetic order is used in both factors.
    for j in (.5, 1., 2., 8.):
        sp = spin_matrices(j)
        north = [np.kron(a, b) for a, b in zip(pauli, sp)]
        offset = np.kron(pauli[2], np.eye(round(2*j+1)))
        def eigen(x, y):
            radii = [np.hypot(1+x, y), np.hypot(1-x, y), 1.]
            vals = np.linalg.eigvalsh(sum(r*h for r,h in zip(radii, north))-j*offset)
            return vals[np.argmin(abs(vals))]
        step = .003
        c = (4*eigen(step/2, 0)/(step/2)**2-eigen(step, 0)/step**2)/3
        np.testing.assert_allclose(c, -1., atol=2e-8)
        np.testing.assert_allclose(eigen(0, .12), 0., atol=1e-13)
        if j == .5:
            x, y = .13, .09
            p, m = np.hypot(1+x, y), np.hypot(1-x, y)
            np.testing.assert_allclose(eigen(x, y), .5-np.hypot(.5,(p-m)/2), atol=1e-14)
        rows.append(dict(spin=j, axial_second_order_coefficient=float(c)))
    return rows


def nonlinear_geometry(asymmetry):
    """Three independent turning planes of the exact six-matrix C1 ansatz."""
    axes = np.array([1+asymmetry, 1-asymmetry, 1.])
    q = np.column_stack((axes, np.zeros(3)))
    p = np.column_stack((np.zeros(3), np.full(3, .5)))
    def rhs(t, y):
        q, p = y.reshape(2, 3, 2)
        lengths = np.sum(q*q, axis=1)
        return np.array([p, -(lengths.sum()-lengths)[:,None]*q]).ravel()
    sol = solve_ivp(rhs, (0., 12.), np.array([q, p]).ravel(), method="DOP853",
                    max_step=.026, rtol=3e-13, atol=1e-15, dense_output=True)
    assert sol.success
    def state(t):
        q, p = sol.sol(abs(t)).reshape(2, 3, 2)
        if t<0:
            return q*[1,-1], p*[-1,1]
        return q, p
    def invariants(q, p):
        radii = np.sum(q*q, axis=1)
        energy = (np.sum(p*p)+sum(radii[i]*radii[l] for i,l in ((0,1),(1,2),(2,0))))/2
        return energy, q[:,0]*p[:,1]-q[:,1]*p[:,0]
    energy, angular = invariants(q,p)
    for t in np.linspace(0,12,61):
        e, ell = invariants(*state(t))
        np.testing.assert_allclose(np.r_[e,ell], np.r_[energy,angular], atol=2e-11)

    def metric(point, pole):
        t, _, x, y = point
        n3 = np.sqrt(1-x*x-y*y)
        n = np.array([x, y, n3])
        q, p = state(t)
        # Cyclic permutations give regular charts at any of the three poles.
        q, p = np.roll(q,2-pole,axis=0), np.roll(p,2-pole,axis=0)
        target = np.column_stack(((n[:,None]*p).ravel(), np.zeros(6),
                                  (np.array([1.,0.,-x/n3])[:,None]*q).ravel(),
                                  (np.array([0.,1.,-y/n3])[:,None]*q).ravel()))
        induced = target.T@target
        induced[1,1] = -1.
        poisson = np.array([[0,1,0,0],[-1,0,0,0],[0,0,0,n3],[0,0,-n3,0]])
        density = poisson@induced@poisson.T/n3
        return np.sqrt(-np.linalg.det(density))*np.linalg.inv(density)
    def ricci(step, x=0., y=0., pole=2):
        origin = np.array([0.,0.,x,y])
        def local(delta):
            return metric(origin+delta,pole)
        metric0 = local(np.zeros(4))
        inv = np.linalg.inv(metric0)
        deltas = step*np.eye(4)
        dg = np.empty((4,4,4))
        d2 = np.empty((4,4,4,4))
        for i, ei in enumerate(deltas):
            gp, gm = local(ei), local(-ei)
            dg[i] = (gp-gm)/(2*step)
            for l, el in enumerate(deltas):
                if i==l:
                    d2[i,l] = (gp+gm-2*metric0)/step**2
                else:
                    d2[i,l] = (local(ei+el)-local(ei-el)-local(-ei+el)+local(-ei-el))/(4*step**2)
        def first_kind(d):
            return (d.transpose(2,0,1)+d.transpose(2,1,0)-d)/2
        lower = first_kind(dg)
        conn = np.einsum("rl,lab->rab", inv, lower)
        deriv = np.array([np.einsum("rl,lab->rab",-inv@dg[k]@inv, lower)
                          +np.einsum("rl,lab->rab",inv,first_kind(d2[k])) for k in range(4)])
        ric = (np.einsum("rrab->ab",deriv)-np.einsum("brar->ab",deriv)
               +np.einsum("rrl,lab->ab",conn,conn)-np.einsum("rbl,lar->ab",conn,conn))
        ray = np.array([1/np.sqrt(-metric0[0,0]),1/np.sqrt(metric0[1,1]),0.,0.])
        return float(ray@ric@ray)
    step = .0008*min(1.,min(axes)/.5)
    coarse, fine = ricci(step), ricci(step/2)
    assert abs(coarse-fine)<2e-5*max(1.,abs(fine))
    null = (4*fine-coarse)/3
    if asymmetry==0.:
        np.testing.assert_allclose(null,-28.,atol=1.5e-7)
    speed = .5
    a1, a2, _ = axes
    s = a1*a1+a2*a2
    dens = speed*a1*a2
    wjet = s*s/speed**2-s
    vjet = (wjet+speed**2/a1**2-a2**2-1+speed**2/a2**2-a1**2-1)/2
    springs = np.sum(axes**2)-axes**2
    curvatures = springs*(springs*axes**2-speed**2)
    def optical(n):
        lapse2 = speed*np.prod(axes)*np.linalg.norm(n/axes)
        return -np.dot(n*n,curvatures)/(speed**2*lapse2)
    normals = [np.eye(3)[i] for i in range(3)]
    mixed = np.array([.42,.36,np.sqrt(1-.42**2-.36**2)])
    direct = (4*ricci(step/2,*mixed[:2])-ricci(step,*mixed[:2]))/3
    poles = [(4*ricci(step/2,pole=i)-ricci(step,pole=i))/3 for i in (0,1)]+[null]
    np.testing.assert_allclose(poles+[direct],[optical(n) for n in normals]+[optical(mixed)],
                               atol=1e-6,rtol=0.)
    return dict(initial_shape_asymmetry=asymmetry, energy=energy, individual_angular_momenta=angular.tolist(),
                uniform_lower_matrix_radius=float(min(abs(angular))/np.sqrt(2*energy)),
                uniform_upper_matrix_radius=float(2*energy/min(abs(angular))),
                north_area_proper_acceleration=wjet/dens, north_volume_proper_acceleration=vjet/dens,
                north_null_ricci=float(null), richardson_input_difference=abs(coarse-fine),
                axis_null_ricci=[float(optical(n)) for n in normals], axis_ricci_from_metric=poles,
                off_axis_null_ricci_from_metric=direct, off_axis_null_ricci_from_optics=float(optical(mixed)))


def records_and_circle(shear_row):
    rho = shear_row["measured_mode_fraction"]
    g2 = 1/(1e9*(2*np.pi)**2*.02**4)
    variance = shear_row["times_inertia_vacuum_shape_variance"]*g2/4
    relative_mass = .75/g2
    blur = np.sqrt(-START/relative_mass)
    def comparison(s):
        phi = lambda x: np.exp(-x*x/2)/np.sqrt(2*np.pi)
        def integral(fn):
            return 2*quad(fn,0,1,epsabs=1e-13)[0]+2*quad(fn,1,12,epsabs=1e-13)[0]
        prob0 = integral(lambda z: phi(z)*ndtr((z*z-1)/s))
        prob1 = integral(lambda z: phi(z)*(1-rho+rho*z*z)*ndtr((z*z-1)/s))
        by_parts = 2*rho/s*integral(lambda z: z*z*phi(z)*phi((z*z-1)/s))
        np.testing.assert_allclose(prob1-prob0,by_parts,atol=2e-12)
        return dict(axial_noise_in_shape_variances=s, vacuum=prob0, absorbed=prob1,
                    difference=by_parts, difference_bound=2*rho/(s*np.sqrt(2*np.pi)))
    aperture = [comparison(s) for s in (.1,1.,10.,blur/variance)]
    budgets = []
    for K in (0,1,2,4,8):
        size = 2*K+1
        operator = (np.diag(np.ones(size-1),1)+np.diag(np.ones(size-1),-1))/2
        values, vectors = np.linalg.eigh(operator)
        wave = np.sin(np.pi*np.arange(1,size+1)/(size+1))*np.sqrt(2/(size+1))
        np.testing.assert_allclose(abs(vectors[:,-1]@wave), 1., atol=1e-13)
        np.testing.assert_allclose(values[-1],np.cos(np.pi/(size+1)),atol=1e-14)
        budgets.append(dict(largest_exchange=K, best_first_moment=float(values[-1]),
                            zero_transfer_probability=float(wave[K]**2)))
    unbounded = []
    modes = np.arange(-80,81)
    for beta in (1.,3.,8.):
        weights = iv(modes,beta)**2/iv(0,2*beta)
        visibility = iv(1,2*beta)/iv(0,2*beta)
        np.testing.assert_allclose([sum(weights), weights@(modes**2)],[1., beta*visibility/2],atol=2e-14)
        unbounded.append(dict(concentration=beta, angular_visibility=visibility,
                              squared_transfer=weights@(modes**2),
                              outside_positive_rank_3_plus_4=float(sum(weights[(modes < -2)|(modes>3)]))))
    return dict(gauge_coupling_squared=g2, shape_variance=variance,
                unsqueezed_free_point_minimum_width=blur,
                relative_velocity_spread_at_unit_blur=1/(2*relative_mass*variance),
                finite_resolution=aperture, finite_momentum_bands=budgets, circular_windows=unbounded,
                seven_units_two_positive_ranks_visibility=float(np.cos(np.pi/7)))


def main():
    receiver = Receiver(1.)
    rows = [receiver.measure(k, 40) for k in (1., 4., 8.)]
    refined = receiver.measure(4., 63)
    assert max(abs(np.array(rows[1]["left_charge_weights"])-refined["left_charge_weights"])) < 2e-12
    sources = [collective_emitter(n) for n in (750, 1500, 3000)]
    for key in sources[0]:
        assert abs(sources[-1][key]-sources[-2][key]) < 1.5e-5
    shears = [shear(k) for k in (1., 4., 8.)]
    ranks = [axial_blocks(j,60) for j in (1.,4.,8.,16.,32.)]
    np.testing.assert_allclose(ranks[0]["left_absorbed_coefficient"],rows[1]["left_charge_weights"][0],atol=3e-12)
    high = axial_blocks(32.,83)
    for key in ("left_absorbed_coefficient","highest_axial_block_coefficient"):
        np.testing.assert_allclose(ranks[-1][key],high[key],atol=2e-11)
    result = dict(ordinary_and_quantized_tide=rows, oscillator_fock_residual=fock_ordering_test(),
                  stationary_resonant_receiver=stationary_and_source(), rotating_source_grids=sources,
                  intrinsic_shear=shears, oriented_pole=north_spectrum(),
                  finite_resolution_and_circle=records_and_circle(shears[1]),
                  nonlinear_interiors=[nonlinear_geometry(x) for x in (0., .15, .3, .5, .8)],
                  all_directions_defocus_until=brentq(lambda e:(1-e)**2*((1+e)**2+1)-.25,0,1),
                  all_magnetic_blocks=ranks)
    path = Path(__file__).resolve().parents[1]/"verification/cat-graviton-port-results.json"
    path.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
    print("Computed the matrix interiors, matter response, finite-resolution comparisons and momentum bands.")


def figure(path):
    import matplotlib.pyplot as plt
    path_data = Path(__file__).resolve().parents[1]/"verification/cat-graviton-port-results.json"
    data = json.loads(path_data.read_text(encoding="utf8"))
    cases = data["nonlinear_interiors"]
    records = data["finite_resolution_and_circle"]
    fig, axes = plt.subplots(1, 3, figsize=(9., 3.0), layout="constrained")
    x = [r["initial_shape_asymmetry"] for r in cases]
    axes[0].plot(x, [-r["north_null_ricci"] for r in cases], "o-", color="#235578", label="North pole")
    axes[0].plot(x, [-r["axis_null_ricci"][1] for r in cases], "s--",
                 color="#945024", label="Short-axis pole")
    axes[0].axhline(0,color=".5",linewidth=.7)
    axes[0].set(xlabel="Initial ellipticity", ylabel="Negative null Ricci curvature", title="Turning interior")
    axes[0].legend(frameon=False, fontsize=8)
    blur = records["finite_resolution"]
    axes[1].semilogx([r["axial_noise_in_shape_variances"] for r in blur],
                      [r["difference"] for r in blur], "o-", color="#235578")
    axes[1].set(xlabel="Axial width / shape variance", ylabel="Change in gap-sign probability",
                title="Material resolution", ylim=(-.02,.53))
    budgets = records["finite_momentum_bands"]
    axes[2].plot([r["largest_exchange"] for r in budgets],
                 [r["best_first_moment"] for r in budgets], "D-", color="#416941")
    axes[2].set(xlabel="Allowed exchange in each direction", ylabel="Maximum angular visibility",
                title="Proposed M circle", ylim=(-.04,1.05))
    for ax in axes:
        ax.spines[["right", "top"]].set_visible(False)
        ax.tick_params(labelsize=8)
    fig.savefig(path, metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path, help="Build the publication figure from the numerical table")
    args = parser.parse_args()
    if args.figure:
        figure(args.figure)
    else:
        main()
