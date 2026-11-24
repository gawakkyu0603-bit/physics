"""Kähler freedom of the flux sectors and tidal index crossings in ordinary matter."""
import itertools
import json
from collections import Counter
from fractions import Fraction
from math import comb, lcm
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy.special import ndtri
from scipy.stats import qmc

from cat_vacua_sky import torus_fluxes


def integer_kernel(matrix):
    """Columns span the rational kernel. Clear denominators in each column."""
    rows = [[Fraction(int(x)) for x in row] for row in matrix]
    cols = matrix.shape[1]
    pivots = []
    for col in range(cols):
        pivot = next((i for i in range(len(pivots),len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        i = len(pivots)
        rows[i], rows[pivot] = rows[pivot], rows[i]
        scale = rows[i][col]
        rows[i] = [e/scale for e in rows[i]]
        for j, row in enumerate(rows):
            if j != i and row[col]:
                multiple = row[col]
                rows[j] = [a-multiple*b for a,b in zip(row,rows[i])]
        pivots.append(col)
    basis = []
    for col in range(cols):
        if col not in pivots:
            vector = [Fraction(int(j == col)) for j in range(cols)]
            for i,pivot in enumerate(pivots):
                vector[pivot] = -rows[i][col]
            denominator = lcm(*(e.denominator for e in vector))
            basis.append([int(e*denominator) for e in vector])
    return np.array(basis,dtype=np.int64).reshape(-1,cols).T


def kahler_constraints(hodge, triples):
    # Three diagonal (1,1) forms and the real and imaginary parts for each pair.
    forms = [[(2*i,2*i+1,1)] for i in range(3)]
    for i,j in itertools.combinations(range(3),2):
        forms.extend([[(2*i,2*j,1),(2*i+1,2*j+1,1)],
                      [(2*i+1,2*j,1),(2*i,2*j+1,-1)]])
    wedge = np.zeros((20,6,9),dtype=np.int64)
    for i, triple in enumerate(triples):
        for col, terms in enumerate(forms):
            for a,b,coeff in terms:
                word = (a,b)+triple
                if len(set(word)) == 5:
                    missing, = set(range(6))-set(word)
                    inversions = sum(x>y for k,x in enumerate(word) for y in word[k+1:])
                    wedge[i,missing,col] += (-1)**inversions*coeff
    def constraints(F):
        axes = wedge.reshape(20,54)
        return np.concatenate([(F@axes).reshape(-1,6,9),
                               ((F@hodge.T)@axes).reshape(-1,6,9)],axis=1)
    return constraints


def kahler_shapes():
    fluxes, orbits, hodge, triples, fixed = torus_fluxes(include_marked=True)
    constraints = kahler_constraints(hodge, triples)
    equations = constraints(fluxes[fixed].astype(np.int64))
    scale = np.array([1,1,1,0,0,0,0,0,0])
    assert not (equations@scale).any()
    dimensions = 9-np.linalg.matrix_rank(equations)
    marked = Counter(dimensions.tolist())
    orbit_counts = Counter()
    mobile = Counter()
    anchor_flux = None
    pairs = Counter()
    def shared_dimensions(kernel):
        dim = kernel.shape[1]
        for indices in itertools.combinations(range(dim),dim-1):
            trial = np.column_stack([scale,kernel[:,indices]])
            if integer_kernel(trial).shape[1] == 0:
                shape = trial[:,1:]
                break
        mats = equations@shape
        gram = mats.transpose(0,2,1)@mats
        bound = int(np.max(np.abs(gram)))
        assert 6*bound**3 < np.iinfo(np.int64).max
        second = sum(gram[:,i,i]*gram[:,j,j]-gram[:,i,j]**2
                     for i,j in itertools.combinations(range(dim-1),2))
        rank = (np.trace(gram,axis1=1,axis2=2)>0).astype(int)+(second>0)
        assert np.all(second>=0)
        if dim == 4:
            a,b,c,d,e,f = (gram[:,i,j] for i,j in ((0,0),(0,1),(0,2),(1,1),(1,2),(2,2)))
            det = a*(d*f-e*e)-b*(b*f-e*c)+c*(b*e-d*c)
            assert np.all(det>=0)
            rank += det>0
        assert dim in (3,4)
        np.testing.assert_array_equal(rank,np.linalg.matrix_rank(mats))
        return Counter((dim-rank).tolist())
    for orbit in orbits:
        first = orbit[0]
        if not fixed[first]:
            continue
        F = fluxes[first].astype(np.int64)
        norm2 = int(F@F)
        kernel = integer_kernel(constraints(F[None,:])[0])
        dim = kernel.shape[1]
        assert np.all(9-np.linalg.matrix_rank(constraints(fluxes[orbit].astype(np.int64))) == dim)
        orbit_counts[dim] += 1
        for freedom,count in shared_dimensions(kernel).items():
            pairs[freedom] += len(orbit)*count
        mobile[16-2*norm2] += 1
        if norm2 == 8 and dim == 3:
            # Canonical marked anchor, independent of orbit traversal order.
            for f in fluxes[orbit]:
                candidate = tuple(int(t) for t in f)
                if anchor_flux is None or candidate < anchor_flux:
                    anchor_flux = candidate
    pair_hist = {}
    if anchor_flux is not None:
        chosen_anchor = constraints(np.array([anchor_flux]))[0]
        kernel = integer_kernel(chosen_anchor)
        pair_hist = dict(sorted(shared_dimensions(kernel).items()))
    assert sum(pairs.values()) == int(fixed.sum())**2
    return dict(orbit_dimensions=dict(sorted(orbit_counts.items())),
                marked_dimensions=dict(sorted(marked.items())), mobile_D3=dict(sorted(mobile.items())),
                anchor_flux=anchor_flux, shared_metric_dimensions=pair_hist,
                ordered_marked_pair_dimensions=dict(sorted(pairs.items())))


def jacobi_shapes(x):
    return (x**(4/3)+4*x**(-1/3))/5, 2*x**(1/3)-x**(2/3)


def evolve_receiver(q):
    def rhs(x, state):
        a,b,da,db = state
        return [da, db, 4*a/(9*x*x)-2*q*q*b*b*a,
                -2*b/(9*x*x)-q*q*(a*a+b*b)*b]
    sol = solve_ivp(rhs,(1.,.001),(1.,1.,0.,0.),method="DOP853",
                    rtol=2e-12,atol=3e-14,dense_output=True)
    assert sol.success
    return sol.sol


def su2(rank):
    j = (rank-1)/2
    m = np.arange(rank)-j
    raising = np.diag(np.sqrt((j-m[:-1])*(j+m[:-1]+1)),-1)
    return np.array([(raising+raising.T)/2,(raising-raising.T)/(2j),np.diag(m)])


def retarded_primitive(radius_in_horizon_units):
    y = np.sqrt(radius_in_horizon_units)
    return 2*(y**3/3+y*y/2+y+np.log(y-1))


def falling_indices():
    pauli = 2*su2(2)
    output = []
    for q in (0., .1, .3, .6):
        profile = evolve_receiver(q)
        if q == 0:
            x = np.geomspace(.004,1.,50)
            np.testing.assert_allclose(profile(x)[:2],jacobi_shapes(x),rtol=2e-10)
        for rank in (2,3,4,6,8):
            j = (rank-1)/2
            generators = su2(rank)
            # Complex probe-root block; its adjoint is not a second independent root.
            xx, yy, zz = [np.kron(s,g) for s,g in zip(pauli,generators)]
            for x in (.04,.08,.16,.32,.64):
                a,b = profile(x)[:2]
                eig = np.linalg.eigvalsh(b*(xx+yy)+a*zz)
                k = np.arange(-j,j)+.5
                rad = np.sqrt(a*a*k*k+b*b*((j+.5)**2-k*k))
                analytic = np.r_[a*j,a*j,-a/2+rad,-a/2-rad]
                np.testing.assert_allclose(eig,np.sort(analytic),atol=3e-13)
            if rank%2:
                continue
            def distance(x):
                a,b = profile(x)[:2]
                return a-rank*b
            cross = brentq(distance,.001,1.,xtol=5e-15)
            a,b,da,db = profile(cross)
            eps = .001*cross
            def trace_sign(x):
                aa,bb = profile(x)[:2]
                return int(np.sign(np.linalg.eigvalsh(bb*(xx+yy)+aa*zz)).sum())//2
            assert trace_sign(cross+eps)==1 and trace_sign(cross-eps)==0
            # The K=0 spin block has constant eigenvectors for the entire fall.
            # The first spin coordinate of our ascending-m Pauli basis is spin down.
            k0_indices = [rank//2, rank+rank//2-1]
            half_block=(b*(xx+yy)+a*zz)[np.ix_(k0_indices,k0_indices)]
            np.testing.assert_allclose(half_block,[[-a/2,rank*b/2],[rank*b/2,-a/2]],atol=2e-13)
            radius_fraction = cross**(2/3)
            row = dict(q=q,rank=rank,proper_time_remaining_fraction=cross,
                       radius_fraction=radius_fraction,
                       start_radius_for_horizon_crossing=1/radius_fraction,
                       slope_in_x=(rank*db-da)/2)
            if 10*radius_fraction>1.5:
                row["retarded_lead_vs_1p5_horizon"]=float(
                    retarded_primitive(10*radius_fraction)-retarded_primitive(1.5))
            output.append(row)
    return output


def canonical_occupation(rank, beta_a):
    """Exact total relative U(1) charge. Four rising modes are singled out."""
    j = (rank-1)/2
    groups = [(4*(rank+1)-4,-j),(4*(rank+1),j),
              (4*(rank-1),-j-1),(4*(rank-1),j+1)]
    # Use common energy offsets per group to avoid overflow; they cancel in all ratios.
    def coefficients(n, energy):
        return np.array([comb(n,k)*np.exp(-beta_a*energy*k-max(0,-beta_a*energy*n))
                         for k in range(n+1)])
    weights=np.array([1.])
    for n,energy in groups:
        weights=np.convolve(weights,coefficients(n,energy))
    four=coefficients(4,-j)
    total=8*rank
    prob=np.array([weights[total-k]*four[k] for k in range(5)])
    prob/=prob.sum()
    if beta_a == 0:
        np.testing.assert_allclose(prob[0],comb(16*rank-4,total)/comb(16*rank,total))
    return dict(rank=rank,beta_a=beta_a,probability_none=prob[0],
                probability_all=prob[-1],mean_occupied=prob@np.arange(5))


def displaced_points():
    x_horizon = 10**-1.5
    a_h,b_h = jacobi_shapes(x_horizon)
    aspect = a_h/b_h
    axis_coverage = {}
    for rank in range(2,10):
        centres = np.arange(rank-1)-(rank-2)/2
        widths = np.sqrt(np.maximum(0.,1-(rank**2-4*centres**2)/aspect**2))
        fraction = float(np.sum(widths)/(rank-1))
        offsets = np.linspace(-(rank-1)/2,(rank-1)/2,20001)
        inside = np.any((offsets[:,None]-centres)**2*4+
                        (rank**2-4*centres**2)/aspect**2 < 1,axis=1)
        assert abs(fraction-inside.mean()) < 4e-4
        axis_coverage[str(rank)] = fraction

    # Propagate one initially filled, negative-energy spinor through the
    # time-dependent axial block for a comoving point at finite offset.
    spin_x=np.array([[0.,1.],[1.,0.]])
    spin_z=np.diag([1.,-1.])
    output=[]
    for rank,q,offset,k in ((2,.1,.2,0.),(2,.3,.3,0.),(3,.1,.5,.5),
                             (3,.3,.65,.5),(4,.1,.86,1.)):
        profile=evolve_receiver(q)
        coefficient=np.sqrt((rank/2)**2-k*k)
        def entries(x):
            a,b=profile(x)[:2]
            d=offset*jacobi_shapes(x)[0]
            return a,b*coefficient,a*k-d
        def level_gap(x):
            a,off,diagonal=entries(x)
            return np.hypot(off,diagonal)-a/2
        grid=np.geomspace(1,.003,110)
        brackets=[(b,a) for a,b in zip(grid[:-1],grid[1:]) if level_gap(a)*level_gap(b)<0]
        if not brackets:
            raise ValueError("no displaced crossing for requested preparation")
        x=brentq(level_gap,*brackets[0])
        # Opposite chirality: negative eigenvalue before the crossing becomes positive.
        def H(x):
            a,off,diagonal=entries(x)
            return a*np.eye(2)/2-off*spin_x-diagonal*spin_z
        initial=np.linalg.eigh(H(1.))[1][:,0]
        reading=np.linalg.eigh(H(x))[1][:,0]
        sol=solve_ivp(lambda t,y: 1j*q*H(t)@y,(1.,x),initial.astype(complex),
                      method="DOP853",rtol=3e-12,atol=5e-14)
        evolved=sol.y[:,-1]
        np.testing.assert_allclose(np.linalg.norm(evolved),1.,atol=5e-12)
        occupied=abs(np.vdot(reading,evolved))**2
        # Independent midpoint propagation with exact two-component exponentials.
        wave=initial.astype(complex)
        edges=np.linspace(1.,x,3001)
        for left,right in zip(edges[:-1],edges[1:]):
            a,off,diagonal=entries((left+right)/2)
            mag=np.hypot(off,diagonal)
            angle=q*(right-left)*mag
            wave=(np.cos(angle)*wave-1j*np.sin(angle)*(off*spin_x+diagonal*spin_z)@wave/mag)
        np.testing.assert_allclose(abs(np.vdot(reading,wave))**2,occupied,rtol=0,atol=5e-8)
        output.append(dict(rank=rank,q=q,offset=offset,k=k,radius_fraction=x**(2/3),
                           probability_rising_occupied=occupied,all_four_empty=(1-occupied)**4))
    return dict(jacobi_horizon_aspect=aspect,coverage_at_start_ten=axis_coverage,weights=output)


def radiative_flavors():
    # Six real Clifford polarizations between the two chiral four-dimensional
    # internal multiplets. They are orthogonal coordinates of the ordinary layer.
    pairs = list(itertools.combinations(range(4),2))
    antisymmetric = {}
    for i,j in pairs:
        m=np.zeros((4,4))
        m[i,j],m[j,i]=1.,-1.
        antisymmetric[i,j]=m
    cartesians=[]
    for p,r,orientation in (((0,1),(2,3),1),((0,2),(1,3),-1),((0,3),(1,2),1)):
        a,b=antisymmetric[p],orientation*antisymmetric[r]
        cartesians.extend([a+b,1j*(a-b)])
    for i,a in enumerate(cartesians):
        for j,b in enumerate(cartesians):
            np.testing.assert_allclose(a.conj().T@b+b.conj().T@a,2*(i==j)*np.eye(4))
    isometry=np.vstack(cartesians)/np.sqrt(6)
    np.testing.assert_allclose(isometry.conj().T@isometry,np.eye(4))
    for i,j in itertools.product(range(4),repeat=2):
        rho=np.eye(4)[:,i,None]@np.eye(4)[None,j,:]
        joint=isometry@rho@isometry.conj().T
        core=np.trace(joint.reshape(6,4,6,4),axis1=0,axis2=2)
        np.testing.assert_allclose(core,(np.trace(rho)*np.eye(4)-rho.T)/3,atol=1e-15)
    rho_difference=np.diag([1.,-1.,0.,0.])
    joint=(isometry@rho_difference@isometry.conj().T).reshape(6,4,6,4)
    def distance(m):
        return float(np.sum(np.abs(np.linalg.eigvalsh(m)))/2)
    a=distance(np.trace(joint,axis1=0,axis2=2))
    b=distance(np.trace(joint,axis1=1,axis2=3))
    both=distance(joint.reshape(24,24))
    np.testing.assert_allclose([a,b,both],[1/3,2/3,1.])
    return dict(core_trace_distance=a,emitted_mode_trace_distance=b,joint_trace_distance=both)


def unaligned_rank_two():
    """Invariant ensemble of classical initial shapes at fixed Frobenius size."""
    a,b=jacobi_shapes(10**-1.5)
    endpoint=(a/b)**2
    pauli=2*su2(2)
    products=np.array([np.kron(x,y) for x in pauli for y in pauli])
    fractions=[]
    for seed in range(169,177):
        points=qmc.Sobol(9,scramble=True,seed=seed).random_base2(14)
        raw=ndtri(points)
        shapes=(raw/np.linalg.norm(raw,axis=1)[:,None]).reshape(-1,3,3)
        gram=shapes@shapes.transpose(0,2,1)
        # Along the Jacobi orbit only the third row scales, by sqrt(t).
        r=gram[:,2,2]
        trace=gram[:,0,0]+gram[:,1,1]
        A=r**2
        B=4*np.sum(gram[:,:2,2]**2,axis=1)-2*r*trace
        C=(gram[:,0,0]-gram[:,1,1])**2+4*gram[:,0,1]**2
        initial=A+B+C
        final=A*endpoint**2+B*endpoint+C
        turning=-B/(2*A)
        steps=(initial*final<0).astype(int)
        steps+=2*((initial>0)&(final>0)&(turning>1)&(turning<endpoint)&(4*A*C-B**2<0))
        for scaled,discriminant in ((1.,initial),(np.sqrt(endpoint),final)):
            sample=shapes[:32].copy()
            sample[:,2,:]*=scaled
            direct=np.linalg.eigvalsh(np.einsum('ni,ijk->njk',sample.reshape(-1,9),products))
            nonzero=np.abs(np.sign(direct).sum(axis=1)) == 2
            np.testing.assert_array_equal(nonzero,discriminant[:32]<0)
        fractions.append(np.bincount(steps,minlength=3)/len(steps))
    values=np.array(fractions)
    return dict(points_per_scramble=2**14,scrambles=len(values),
                mean_crossing_counts=values.mean(axis=0).tolist(),
                between_scramble_sd=values.std(axis=0,ddof=1).tolist())


if __name__ == "__main__":
    result = dict(kahler=kahler_shapes(), crossing=falling_indices(), displaced=displaced_points(),
                  transverse_emission=radiative_flavors(),
                  unaligned_shapes=unaligned_rank_two(),
                  occupation=[canonical_occupation(n,t) for n in (2,4,6) for t in (0.,1.,4.)])
    target=Path(__file__).resolve().parents[1]/"verification"/"cat-tidal-crossing-results.json"
    target.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
