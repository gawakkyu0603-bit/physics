"""Reproduce the charge, scalar and matter calculations at the cubic six-torus."""
import json
from itertools import combinations, product
from math import gcd
from pathlib import Path

import numpy as np
from cat_dyon_radius import laboratory


PAIRS = list(combinations(range(8), 2))
FOURS = [s for s in combinations(range(8), 4) if 0 in s]
STAR = [(0, 1), (0, 2), (0, 3)]
TRIANGLE = [(0, 1), (0, 2), (1, 2)]
WEIGHTS = np.array([.18, .31, .51])


def complement(indices, size):
    return tuple(i for i in range(size) if i not in indices)


def parity(indices):
    return (-1)**sum(a > b for a, b in combinations(indices, 2))


def skew_unit(size, pair):
    mat = np.zeros((size, size))
    i, j = pair
    mat[i, j], mat[j, i] = 1, -1
    return mat


def lorentz_charge_planes():
    """Six Euclidean Clebsch matrices for the nonzero SU(4) charge block."""
    gamma = []
    for p in STAR:
        cp = complement(p, 4)
        a, b = skew_unit(4, p), parity(p+cp)*skew_unit(4, cp)
        gamma += [a+b, -1j*(a-b)]
    for i, g in enumerate(gamma):
        for j, h in enumerate(gamma):
            assert np.allclose(g @ h.conj().T+h @ g.conj().T, 2*(i == j)*np.eye(4))
    for j, p in enumerate(STAR):
        for sign in (1, -1):
            z = (gamma[2*j]+1j*sign*gamma[2*j+1])/2
            ix = p if sign == 1 else complement(p, 4)
            assert np.array_equal(abs(z), abs(skew_unit(4, ix)))


def scalar_generators():
    """Real coset coordinates. Each has a complex four-form and its signed dual."""
    basis = []
    for s in FOURS:
        cs = complement(s, 8)
        for unit in (1, 1j):
            values = {s: unit, cs: parity(s+cs)*np.conj(unit)}
            gen = np.zeros((28, 28), complex)
            for a, u in enumerate(PAIRS):
                for b, v in enumerate(PAIRS):
                    ix = u+v
                    gen[a, b] = parity(ix)*values.get(tuple(sorted(ix)), 0)
            assert np.array_equal(gen, gen.T)
            basis.append(gen)
    return np.array(basis)


def incidence(s, pair):
    return int(set(pair).issubset(s) or set(pair).isdisjoint(s))


def frame(name, planes, weights, basis, rng):
    # First mass derivative vanishes. The second is the squared norm of the
    # first derivative of the complementary charge block at this rank-two point.
    columns = [PAIRS.index(p) for p in planes]
    charge = np.eye(56)[:, columns]
    hessian = np.zeros((70, 70))
    for weight, column in zip(weights, columns):
        derivative = basis[:, :, column]
        hessian += weight*(derivative @ derivative.conj().T).real
    expected = np.array([sum(w*incidence(s, p) for p, w in zip(planes, weights))
                         for s in FOURS for _ in range(2)])
    assert np.allclose(hessian, np.diag(expected), atol=1e-13)
    rr_mask = np.repeat([sum(i < 4 for i in s) % 2 == 1 for s in FOURS], 2)
    ns_values, rr_values = expected[~rr_mask], expected[rr_mask]
    assert len(ns_values) == 38 and len(rr_values) == 32

    # Independent check using actual skew singular values after exponentiation.
    errors = np.zeros(2)
    directions = rng.normal(size=(20, 70))
    i_upper, j_upper = np.array(PAIRS).T
    for direction in directions:
        direction /= np.linalg.norm(direction)
        tensor = np.einsum('m,mij->ij', direction, basis)
        generator = np.block([[tensor.real, tensor.imag], [tensor.imag, -tensor.real]])
        eigenvalues, modes = np.linalg.eigh(generator)
        coeff = modes.T @ charge

        def gas_energy(t):
            v = modes @ (np.exp(t*eigenvalues)[:, None]*coeff)
            blocks = np.zeros((len(planes), 8, 8), complex)
            blocks[:, i_upper, j_upper] = (v[:28]+1j*v[28:]).T
            blocks -= blocks.transpose(0, 2, 1).copy()
            return np.dot(weights, np.linalg.svd(blocks, compute_uv=False)[:, 0])

        for i, t in enumerate((.012, .006)):
            fd = (gas_energy(t)+gas_energy(-t)-2*sum(weights))/t**2
            errors[i] = max(errors[i], abs(fd-np.dot(expected, direction**2)))
    assert errors[0] < 2.e-5 and errors[1] < 6.e-6
    # A finite geodesic in any common null direction fixes all charge vectors.
    flat = np.flatnonzero(expected == 0)
    if len(flat):
        direction = rng.normal(size=len(flat))
        tensor = np.einsum('m,mij->ij', direction, basis[flat])
        assert np.array_equal(tensor[:, columns], np.zeros((28, len(columns))))

    def multiplicities(values):
        unique, counts = np.unique(values.round(10), return_counts=True)
        return {f'{v:.6f}': int(count) for v, count in zip(unique, counts)}

    return dict(frame=name, ns=multiplicities(ns_values), rr=multiplicities(rr_values),
                positive=int(np.sum(expected > 0)), flat=len(flat),
                finite_difference_errors=[float(f'{e:.3g}') for e in errors])


def primitive_index():
    """Sen's charge invariants and Jacobi-product coefficient at q^1 y^0."""
    rows = []
    for j, sign in product(range(3), (1, -1)):
        q, p = np.zeros(12, int), np.zeros(12, int)
        q[[2*j, 2*j+6]] = 1
        p[[2*j+1, 2*j+7]] = sign
        inner = lambda u, v: int(u[:6] @ v[6:]+u[6:] @ v[:6])
        q2, p2, qp = inner(q, q), inner(p, p), inner(q, p)
        charge = np.r_[q, p]
        triple = np.r_[q2*p-qp*q, -p2*q+qp*p]
        chi = gcd(*(int(x) for x in (np.outer(charge, triple)-np.outer(triple, charge)).flat))
        psi = gcd(q2//2, p2//2, qp, *(int(x) for x in (np.outer(q, p)-np.outer(p, q)).flat))
        delta = q2*p2-qp**2
        assert (delta, psi, chi) == (4, 1, 2)
        rows.append([j+1, sign, delta, psi, chi])
    # (y^-1-2+y)(1+q(4-2y-2y^-1)) from the product through first order.
    constant = {0: -2, 1: 1, -1: 1}
    first = {0: 4, 1: -2, -1: -2}
    coefficient = sum(v*first[-m] for m, v in constant.items())
    assert coefficient == -12
    return dict(charges=rows, jacobi_q1_y0=coefficient, absolute_index=abs(coefficient))


def flux_matrix(k):
    zero = np.zeros_like(k)
    return np.block([[zero, k], [-k.T, zero]])


def gauge_log_alpha(metric, two_form, flux, dilaton):
    return (dilaton+.25*np.linalg.slogdet(metric)[1]
            -.5*np.linalg.slogdet(metric+two_form+flux)[1])


def volume_stack(a, b):
    # At r=1 this stack aligns with both light-matter stacks in disk DBI.
    # Its four-dimensional energy above the real calibration varies with r.
    c = np.array([[0, 1, 0], [1, 2, 0], [0, 0, -1]])
    def excess(u):
        r = np.exp(u)
        z = np.linalg.det(r**2*np.eye(3)+1j*c)
        assert np.allclose(z, r**6+3*r**2+1j*(r**4-1))
        return r**-3*z.imag**2/(abs(z)+z.real)
    curvatures = [(excess(h)+excess(-h))/h**2 for h in (.002, .001, .0005)]
    assert abs(curvatures[-1]-4) < 4e-6
    def lowest(difference):
        w = abs(np.linalg.eigvalsh(difference))
        return sum(w)-2*max(w)
    angular = 2*np.arctan(np.linalg.eigvalsh(c))
    assert abs(sum(angular)) < 1e-14
    assert abs(sum(abs(angular))-2*max(abs(angular))) < 1e-14
    assert np.allclose([lowest(c-a), lowest(c-b), lowest(2*c)], [-1, -1, -2])
    def rotation(k):
        eye = np.eye(3)
        return (eye+1j*k) @ np.linalg.inv(eye-1j*k)
    angles_ab = np.sort(np.angle(np.linalg.eigvals(rotation(a).conj().T @ rotation(b))))/2
    assert np.allclose(angles_ab/np.pi, [-3/8, 1/8, 1/4])
    for x, y in product([-.5, -.125, .1, .33, .77], repeat=2):
        assert np.isclose(np.arctan((x+y)/(1-x*y)), np.arctan(x)+np.arctan(y))
    return dict(flux=c.tolist(), radial_curvatures=np.round(curvatures, 9).tolist(),
                cubic_point_disk_energy=4, matrix_mass_squared_against_A_B_image=[-1, -1, -2],
                image_relative_angles_over_pi=(angular/np.pi).round(8).tolist(),
                A_B_relative_angles_over_pi=(angles_ab/np.pi).round(8).tolist())


def magnetized_matter(rng):
    a = np.array([[0, -1, 0], [-1, 0, 0], [0, 0, 0]])
    b = np.diag([0, -1, 1])
    relative = b-a
    osc = np.sort(abs(np.linalg.eigvalsh(relative)))
    assert round(np.linalg.det(relative)) == -1 and abs(osc[0]+osc[1]-osc[2]) < 1e-13
    scalar_low = sum(osc)-2*osc
    assert min(scalar_low) > -1e-13
    for scale in [.17, .9, 1., 2.3, 8.5]:
        for k in (a, b):
            assert np.allclose(np.linalg.det(np.eye(3)+1j*scale*k), 1+scale**2)
    # Both degree zero and the relative first Chern class enter the
    # Stueckelberg charge. Equality of every higher character for a copy of A
    # then suffices for the three-stack kernel.
    rr_charges = np.stack([np.r_[1, k.ravel()] for k in (a, b, a)], axis=1)
    assert np.linalg.matrix_rank(rr_charges[:, :2]) == np.linalg.matrix_rank(rr_charges) == 2
    assert np.all(rr_charges @ np.array([1, 0, -1]) == 0)

    max_error = 0.
    total_norm = []
    for flux in [flux_matrix(a), flux_matrix(b)] + [
            (m-m.T) for m in rng.normal(size=(10, 6, 6))]:
        eye = np.eye(6)
        grad = .5*eye-np.linalg.inv(eye+flux).T
        assert np.allclose(4*grad.T @ grad, eye)
        numerical = np.empty_like(grad)
        for i, j in product(range(6), repeat=2):
            dx = np.zeros((6, 6))
            dx[i, j] = 2e-5  # X/2 is canonical, in reduced Planck units
            dg, db = (dx+dx.T)/2, (dx-dx.T)/2
            plus = gauge_log_alpha(eye+dg, db, flux, 0.)
            minus = gauge_log_alpha(eye-dg, -db, flux, 0.)
            numerical[i, j] = (plus-minus)/2e-5
        max_error = max(max_error, np.max(abs(numerical-grad)))
        total_norm.append(.5+np.sum(numerical**2))
    assert max_error < 3.e-9 and np.allclose(total_norm, 2., atol=2e-8)
    atom = laboratory()
    return dict(flux_a=a.tolist(), flux_b=b.tolist(), chiral_index=-1,
                relative_frequencies=osc.round(9).tolist(),
                lowest_vector_masses=(scalar_low.round(9)+0.).tolist(),
                two_stack_massless_abelian=0, three_stack_generator=[1, 0, -1],
                alpha_gradient_norm_squared=2., common_radius_slope=-1.,
                full_em_eta=atom['eta'], volume_dilaton_em_eta=atom['eta']/3,
                free_fall_envelope=atom['normal_95_envelope'],
                dbi_gradient_max_error=float(f'{max_error:.2g}'), volume_fixing=volume_stack(a, b))


def main():
    rng = np.random.default_rng(17970)
    lorentz_charge_planes()
    basis = scalar_generators()
    flat_counts = {}
    for signs in product((1, -1), repeat=3):
        ps = [p if s == 1 else complement(p, 4) for p, s in zip(STAR, signs)]
        flat_counts[''.join('+' if s == 1 else '-' for s in signs)] = 2*sum(
            not any(incidence(f, p) for p in ps) for f in FOURS)
    frames = [frame('shared index', STAR, WEIGHTS, basis, rng),
              frame('cycle', TRIANGLE, WEIGHTS, basis, rng),
              frame('both orientations', STAR+[complement(p, 4) for p in STAR],
                    np.r_[WEIGHTS/2, WEIGHTS/2], basis, rng)]
    assert [f['positive'] for f in frames] == [62, 70, 70]
    result = dict(fractions=WEIGHTS.tolist(), signs_and_flat_counts=flat_counts,
                  frames=frames, quantum_index=primitive_index(), matter=magnetized_matter(rng))
    path = Path(__file__).resolve().parents[1]/'verification'/'cat-charge-orientation-results.json'
    path.write_text(json.dumps(result, indent=2)+'\n', encoding='utf8')


if __name__ == '__main__':
    main()
