"""Compact radii, open magnetic spectra and the scalar force in a D6 matching sector."""
import json
from itertools import product
from pathlib import Path

import numpy as np
from scipy.linalg import eigvalsh
from scipy.optimize import brentq

from cat_dyon_radius import laboratory
from cat_magnetic_orbifold import numerical_hessian


STACKS = np.array([[(1,-1),(2,-1),(1,3)], [(1,1),(0,-1),(1,1)],
                   [(1,1),(1,-1),(1,0)]])
PLANES = np.array([[(1,0),(1,0),(1,0)], [(1,0),(0,1),(0,-1)],
                   [(0,1),(1,0),(0,-1)], [(0,1),(0,-1),(1,0)]])
NUMBERS = np.array([1,1,2])
FILLERS = np.array([4,4,2,6])


def charges(cycle):
    (a,b),(c,d),(e,f) = cycle
    return [a*c*e,-a*d*f,-b*c*f,-b*d*e], [b*d*f,b*c*e,a*d*e,a*c*f]


def central(cycles, shape):
    return np.prod(cycles[:,:,0] + 1j * cycles[:,:,1] * shape, axis=1)


def intersection(first, second):
    return int(np.prod(first[:,0]*second[:,1]-first[:,1]*second[:,0]))


def branes(rng):
    even, odd = (np.array(component) for component in zip(*(charges(c) for c in STACKS)))
    np.testing.assert_array_equal([charges(c)[0] for c in PLANES],np.eye(4))
    assert not np.any([charges(c)[1] for c in PLANES])
    np.testing.assert_array_equal(NUMBERS @ even + FILLERS, [8]*4)
    np.testing.assert_array_equal(NUMBERS @ odd, [2,0,-4,6])
    h = np.array([-1,1,1,1])
    assert np.linalg.matrix_rank(odd) == 3 and not np.any(odd @ h)
    assert np.allclose(central(STACKS,np.ones(3)), [10,2,2])
    pairs = [intersection(STACKS[i], STACKS[j]) for i,j in ((0,1),(0,2),(1,2))]
    assert pairs == [8,6,0] and intersection(STACKS[0],STACKS[2]*[1,-1]) == 0
    def excess(log_shape):
        shape = np.exp(log_shape)
        z = central(STACKS,shape)
        return NUMBERS @ (np.abs(z)-z.real)/np.sqrt(np.prod(shape))
    for log_shape in rng.uniform(-1,1,(24,3)):
        x,y,z = np.exp(log_shape)
        summed = NUMBERS @ central(STACKS,[x,y,z]) + FILLERS @ central(PLANES,[x,y,z])
        assert np.isclose(summed.real,8*(1+x*y+x*z+y*z))
        assert excess(log_shape) >= 0
    jac = np.array([[-5,-4,3],[1,0,1],[1,-1,0]])
    hessian = jac.T @ np.diag(NUMBERS/[10,2,2]) @ jac
    errors = []
    for step in (.004,.002,.001):
        errors.append(np.max(np.abs(numerical_hessian(excess,np.zeros(3),step)-hessian)))
    assert errors[-1]<3e-5 and errors[-1]<.08*errors[0]
    def log_alpha(log_t):
        t = np.exp(log_t)
        shape = [t,t,2*t/(3-t*t)]
        central_values = central(STACKS,shape)
        assert np.isclose(central_values[:2].sum().imag,0) and np.isclose(central_values[2].imag,0)
        return .5*np.log(np.prod(shape))-np.log(abs(central_values[2]))
    assert np.isclose((log_alpha(.0001)-log_alpha(-.0001))/.0002,1)
    mirror = 2*STACKS[0,:,1]/STACKS[0,:,0]
    assert np.isclose(abs(mirror).sum()-2*max(abs(mirror)),-3)
    assert abs(2*np.arctan(mirror/2).sum())<2e-15
    return dict(wrappings=STACKS.tolist(), multiplicities=NUMBERS.tolist(), even=even.tolist(),
        odd=odd.tolist(), fillers=FILLERS.tolist(), remaining_H_lattice_generator=h.tolist(),
        intersections_ab_ac_bc=pairs, hessian=hessian.tolist(),
        eigenvalues=np.linalg.eigvalsh(hessian).tolist(), hessian_fd_errors=errors)


def folded_spectrum(elements, first, last):
    """Hermitian linearization of the discrete strip equation on its reflection quotient."""
    nodes = elements+1
    spacing = np.pi/elements
    weights = np.full(nodes,spacing)
    weights[[0,-1]] *= .5
    gradient = np.diff(np.eye(nodes), axis=0)
    stiffness = (gradient.T @ gradient)/(spacing*np.sqrt(np.outer(weights,weights)))
    values, vectors = np.linalg.eigh(stiffness)
    values[0] = 0.  # The graph Laplacian annihilates constants exactly.
    root = np.kron((vectors*np.sqrt(values)) @ vectors.T, np.eye(len(first)))
    boundary = np.kron(np.diag(np.eye(nodes)[0]/weights[0]),first)
    boundary -= np.kron(np.diag(np.eye(nodes)[-1]/weights[-1]),last)
    pencil = np.block([[boundary,root],[root,np.zeros_like(root)]])
    return eigvalsh(pencil, subset_by_value=(.015,1.52))


def magnetic_response(rng):
    first = np.array([[0.,-1,0],[-1,0,0],[0,0,0]])
    last = np.diag([0.,-1.,1.])
    def cayley(k):
        return np.linalg.solve(np.eye(len(k))-1j*k,np.eye(len(k))+1j*k)
    offsets = np.angle(np.linalg.eigvals(cayley(last).conj().T @ cayley(first)))/(2*np.pi)
    predicted = sorted(v for s in offsets for n in range(-2,3) if .015<(v:=n+s)<1.52)
    errors = {}
    for elements in (12,24,48):
        actual = folded_spectrum(elements,first,last)
        assert len(actual)==len(predicted)
        errors[str(elements)] = float(max(abs(actual-predicted)))
    assert errors['48']<.09*errors['12'] and errors['48']<.001
    # Independent trace of the cyclic shift on reflection-even diagonal fields.
    path = rng.normal(size=9)
    cycle = np.r_[path,path[-2:0:-1]]
    shift = np.roll(np.eye(len(cycle)),1,axis=0)
    commutator = shift @ np.diag(cycle) - np.diag(cycle) @ shift
    assert np.isclose(.5*np.linalg.norm(commutator)**2,np.sum(np.diff(path)**2))
    assert np.isclose(.5*(cycle@cycle),sum(path[1:-1]**2)+.5*(path[0]**2+path[-1]**2))
    points, weights = np.polynomial.legendre.leggauss(32)
    weights *= .5
    covariance_errors = []
    for _ in range(12):
        mid, diff = rng.uniform(-1,1,(2,3))
        fields = mid + points[:,None]*diff/2
        square = fields**2
        cov = (square.T*weights) @ square-np.outer(weights@square,weights@square)
        correction = mid*diff*np.sum(mid*diff)/6 + diff**2*np.sum(diff**2)/360
        assert np.allclose(cov.sum(axis=1)/2,correction,atol=3e-15)
        residuals = []
        for b in (.06,.03):
            volume = np.sqrt(np.prod(1+b*b*square,axis=1))
            reciprocal = 1/(1+b*b*square)
            discrepancy = weights@reciprocal - (weights*volume)@reciprocal/(weights@volume)
            residuals.append(np.linalg.norm(discrepancy/b**4-correction))
        covariance_errors.append(residuals)
    max_errors = np.max(covariance_errors,axis=0)
    assert max_errors[1]<.27*max_errors[0]
    return dict(offsets=sorted(offsets),positive_frequencies=predicted,strip_errors=errors,
        leading_covariance_errors=max_errors.tolist(),mirror_one_plane_at_unity=dict(
        exact=np.pi/4,symmetrized=2*np.arcsinh(1)/(np.sqrt(2)+np.arcsinh(1))))


def geometric_flux():
    """Real structure constants, Jacobi identities, and curvature of the allowed twists."""
    def bracket(twists):
        c = np.zeros((6,6,6),dtype=int)
        for i,k in enumerate(twists):
            j,l = (i+1)%3,(i+2)%3
            for q,r in product(range(2),repeat=2):
                target = 2*i+(q+r)%2
                strength = -k if q+r==0 else k
                c[2*j+q,2*l+r,target] = strength
                c[2*l+r,2*j+q,target] = -strength
        return c
    accepted = 0
    for twists in product(range(-2,3), repeat=3):
        c = bracket(twists)
        twice = np.einsum('ijp,pkl->ijkl',c,c)
        jacobi = twice+twice.transpose(1,2,0,3)+twice.transpose(2,0,1,3)
        valid = not np.any(jacobi)
        assert valid == (np.count_nonzero(twists)<=1)
        accepted += valid
    c = bracket([1,0,0])
    gamma = (c-c.transpose(2,0,1)+c.transpose(1,2,0))/2
    scalar = (np.einsum('jjk,iki',gamma,gamma)-np.einsum('ijk,jki',gamma,gamma)
              -np.einsum('ijk,kji',c,gamma))
    assert scalar==-2
    for cycle in np.concatenate([STACKS,PLANES]):
        tangent = np.zeros((3,6),dtype=int)
        for j in range(3):
            tangent[j,2*j:2*j+2] = cycle[j]
        v = np.einsum('i,j,ijl->l',tangent[1],tangent[2],c)
        assert not np.any(v[2:]) and v[0]*tangent[0,1]==v[1]*tangent[0,0]
    # All allowed even RR forms use zero or two indices from each torus.
    base_count = [sum(choice[1:]) for choice in product(range(2),repeat=3)]
    return dict(accepted_of_125=accepted,unit_scalar_curvature=scalar,
                rr_weights=sorted(-9-3*n for n in base_count),
                massless_tangent_em_norm_squared=4/9)


def scalar_force(rng):
    data = laboratory()
    eta_unit = data['eta']/2  # coefficient for a unit squared canonical EM gradient
    earth_radius, altitude = 6371e3, 710e3
    r_ratio = 1+altitude/earth_radius
    hubble = 70e3/3.085677581491367e22  # illustrative inverse seconds
    cutoff = 299792458/(10*earth_radius)
    fraction = np.sqrt(270/13)*hubble/cutoff
    slope = np.sqrt(6/13)-np.sqrt(2)*fraction
    lower_eta = abs(eta_unit)*slope**2*np.exp(-r_ratio/10)*(1+r_ratio/10)
    # Finite-dimensional positive spectra, arbitrarily mixed with the observable.
    for _ in range(40):
        rates = np.exp(rng.uniform(-4,4,12))
        t = rng.normal(size=12)
        t /= np.linalg.norm(t)
        g = rng.normal(size=12)
        light = rates<=1
        assert abs(g@t)<=np.linalg.norm(g[light])+np.linalg.norm(g)*np.linalg.norm(rates*t)+1e-12
    for _ in range(25):
        rr = rng.uniform(0,1,4)
        powers = np.arange(0,7,2)
        vacuum = -(powers@rr)/9
        curv = (powers*(9+powers))@rr
        assert 99*(-vacuum)<=curv<=135*(-vacuum)
    # Negative internal scalar curvature. Dimensionless potential is a sum of two squares.
    def curved_potential(point):
        u,d = point
        return sum((np.exp(d-k*u/2)-np.exp(2*d+k*u/2))**2 for k in (3,1))
    hessian = np.array([[20,8],[8,4]])
    assert np.allclose(numerical_hessian(curved_potential,np.zeros(2),.00015),hessian,atol=5e-6)
    norms = np.sqrt([1.5,2])
    mass2, axes = np.linalg.eigh(hessian/np.outer(norms,norms))
    assert np.allclose(mass2,(23+np.array([-1,1])*np.sqrt(481))/3)
    photon_weight = axes[1]**2/2
    def sphere(x):
        """Yukawa force divided by Newton's for a uniform spherical Earth."""
        if x < .05:
            form = 1+x*x/10+x**4/280+x**6/15120
            return np.exp(-r_ratio*x)*(1+r_ratio*x)*form
        return (1+r_ratio*x)*3*((x-1)*np.exp(-(r_ratio-1)*x)
            +(x+1)*np.exp(-(r_ratio+1)*x))/(2*x**3)
    def force(scale):
        return abs(eta_unit)*sum(w*sphere(scale*np.sqrt(m)) for w,m in zip(photon_weight,mass2))
    root = brentq(lambda s: force(s)-data['normal_95_envelope'],1,2000)
    hbar_c = 1.973269804e-7  # eV m
    mass_scale = root*hbar_c/earth_radius
    threshold = np.sqrt(mass_scale*2.435e27)/1e9
    longest = earth_radius/(root*np.sqrt(mass2[0]))
    nil_light = np.sqrt(4/9)-np.sqrt(2)*np.sqrt(20)*hubble/cutoff
    nil_force = abs(eta_unit)*nil_light**2*np.exp(-r_ratio/10)*(1+r_ratio/10)
    # Invert the projection inequality at a fixed cutoff. A positive spherical
    # source is at least as effective as a point source of the same charge.
    y = 18.
    laboratory_slope = np.sqrt(data['normal_95_envelope']/abs(eta_unit))
    allowed_at_cut = laboratory_slope/np.sqrt((1+y)*np.exp(-y))
    test_mass_eV = y*hbar_c/(earth_radius+altitude)
    required_mass_eV = test_mass_eV*(2/3-allowed_at_cut)/np.sqrt(2)
    assert required_mass_eV>0
    return dict(eta_massless_dilaton=eta_unit/2,envelope=data['normal_95_envelope'],
        hubble_per_second=hubble,heavy_projection_upper=fraction,
        unscreened_lower_abs_eta=lower_eta,ratio_to_envelope=lower_eta/data['normal_95_envelope'],
        nilmanifold_small_vacuum_lower_abs_eta=nil_force,
        required_correction=dict(cutoff_mr=y,fully_long_range_em_slope_limit=laboratory_slope,
            allowed_light_slope_at_cut=allowed_at_cut,tangent_mass_floor_eV=required_mass_eV,
            tangent_curvature_fourth_root_floor_MeV=np.sqrt(4.5*2.435e27*required_mass_eV)/1e6),
        curved_two_fields=dict(canonical_masses_squared=mass2.tolist(),em_weights=photon_weight.tolist(),
        density_quarter_power_GeV=threshold,range_at_10_TeV_microns=longest*(threshold/1e4)**2*1e6,
        longest_range_km=longest/1e3,
        eta_at_boundary=-force(root),earth_radius_km=earth_radius/1e3,altitude_km=altitude/1e3))


def main():
    rng = np.random.default_rng(180)
    result = dict(branes=branes(rng),magnetic=magnetic_response(rng),geometry=geometric_flux(),
                  force=scalar_force(rng))
    path = Path(__file__).resolve().parents[1]/'verification'/'cat-flux-completion-results.json'
    path.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')


if __name__ == '__main__':
    main()
