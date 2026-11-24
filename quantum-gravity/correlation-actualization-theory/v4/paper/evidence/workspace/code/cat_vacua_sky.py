"""Classical matrix geometries, flat quantum sectors and astronomical tests (volume 5, O)."""
import itertools
import json
from collections import Counter
from math import gcd
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm


def matrix_geometries():
    # Seven BFSS matrices: six rotating coordinates, one compact quotient derivative.
    spin = 1.5
    m = np.arange(-spin, spin+1)
    raising = np.diag(np.sqrt((spin-m[:-1])*(spin+m[:-1]+1)), -1)
    generators = [(raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(m)]
    bracket = lambda a, b: a@b-b@a
    circle_speed = 1.7
    output = []
    for h in (.25, .6, 1., 1.3):
        def rhs(t, state):
            a, b, da, db = state
            return da, db, -2*(a*a+b*b)*a, -2*(a*a+b*b)*b

        solution = solve_ivp(rhs, (0., .025), (1., 0., 0., h), rtol=2e-13,
                             atol=1e-15, dense_output=True)
        a, b, da, db = solution.sol(.022)
        x = [s*j for s in (a, b) for j in generators]
        for matrix in x:
            computed = -sum(bracket(other, bracket(other, matrix)) for other in x)
            np.testing.assert_allclose(computed, -2*(a*a+b*b)*matrix, atol=7e-14)
        gauss = sum(bracket(matrix, s*j) for matrix, (s, j) in
                    zip(x, itertools.product((da, db), generators)))
        np.testing.assert_allclose(gauss, 0., atol=5e-14)
        longitudinal = -.5  # Fourier mode number difference in chosen units below.
        momenta = np.diag([longitudinal, 0., -longitudinal])
        translation = np.diag(np.ones(2), 1)
        mode = np.kron(translation, generators[2])
        x_full = [np.kron(np.eye(3), y) for y in x]
        x_full.append(circle_speed*np.kron(momenta, np.eye(len(m))))
        laplace = sum(bracket(y, bracket(y, mode)) for y in x_full)
        np.testing.assert_allclose(laplace, (circle_speed**2*longitudinal**2+2*(a*a+b*b))*mode,
                                   atol=3e-13)
        # Jacobi estimate from metric samples over four unequal spacings in time.
        times = np.arange(5)*.002
        radius = np.linalg.norm(solution.sol(times)[:2], axis=0)
        log_r = np.log(radius)
        second = np.array([35., -104., 114., -56., 11.])@log_r/(12*.002**2)
        invariant = 2+2*second
        np.testing.assert_allclose(invariant, 2*h*h-2, atol=3e-7)
        output.append(dict(speed=h, curvature_in_sphere_units=2*h*h-2,
                           from_metric_samples=invariant))
    return output


def quantum_sectors():
    # Six unit translations and a glide. Four translations invert; g^2=t_5.
    relations = np.zeros((5, 7), dtype=int)
    for i in range(4):
        relations[i, i] = 2
    relations[4, 4], relations[4, 6] = 1, -2
    # Elementary column addition and permutations are integer-unimodular.
    relations[:, 6] += 2*relations[:, 4]
    smith = relations[[4,0,1,2,3]][:, [4,0,1,2,3,5,6]]
    np.testing.assert_array_equal(smith[:, 5:], np.zeros((5, 2), dtype=int))
    np.testing.assert_array_equal(smith[:,:5], np.diag([1,2,2,2,2]))
    diagonal = [abs(int(smith[i,i])) for i in range(5)]
    assert diagonal == [1, 2, 2, 2, 2]
    grids = {}
    for order in (2, 3, 4, 5):
        count = sum(all(2*s % order == 0 for s in w[:4]) and (w[4]-2*w[6]) % order == 0
                    for w in itertools.product(range(order), repeat=7))
        assert count == order**2*(2 if order % 2 == 0 else 1)**4
        grids[str(order)] = count
    flips = np.zeros((16, 16))
    for state in range(16):
        for bit in range(4):
            flips[state, state ^ (1 << bit)] = -1.
    spectrum, counts = np.unique(np.rint(np.linalg.eigvalsh(flips)).astype(int), return_counts=True)
    assert counts.tolist() == [1,4,6,4,1]
    return dict(smith=diagonal, free_rank=2, torsion_order=16, finite_character_grids=grids,
                illustrative_mixing_spectrum=spectrum.tolist(), multiplicities=counts.tolist())


def flux_mass_ranks(fluxes, representatives, hodge, triples, polarized):
    """Tree-level F-term Jacobian on the axiodilaton and torus period variables."""
    basis = np.eye(6, dtype=complex)
    dz = basis[::2] + 1j*basis[1::2]
    pairs = (list(itertools.combinations_with_replacement(range(3), 2)) if polarized
             else list(itertools.product(range(3), repeat=2)))
    count = len(pairs)
    tangents = np.zeros((count, 3, 6), dtype=complex)
    for k, (i, j) in enumerate(pairs):
        tangents[k, i, 2*j+1] = 1
        if polarized:
            tangents[k, j, 2*i+1] = 1

    def wedge(rows):
        a, b, c = rows
        i, j, k = np.asarray(triples).T
        return (a[i]*(b[j]*c[k]-b[k]*c[j]) + a[j]*(b[k]*c[i]-b[i]*c[k])
                + a[k]*(b[i]*c[j]-b[j]*c[i]))

    omega = wedge(dz)
    d_omega = np.zeros((count, 20), dtype=complex)
    dd_omega = np.zeros((count, count, 20), dtype=complex)
    for a, tangent in enumerate(tangents):
        for i in range(3):
            rows = dz.copy()
            rows[i] = tangent[i]
            d_omega[a] += wedge(rows)
            for b, second_tangent in enumerate(tangents):
                for j in range(3):
                    if i != j:
                        original = rows[j].copy()
                        rows[j] = second_tangent[j]
                        dd_omega[a, b] += wedge(rows)
                        rows[j] = original

    # Integral F wedge Omega = (*F) dot Omega, with no complex conjugation.
    dual_g = fluxes@hodge.T + 1j*fluxes
    assert not (dual_g@omega).any() and not (dual_g@d_omega.T).any()
    assert not (fluxes@omega).any()
    dim = count + 1
    linear_map = np.zeros((len(fluxes), dim, dim), dtype=complex)
    linear_map[:, 0, 1:] = fluxes@d_omega.T
    linear_map[:, 1:, 0] = linear_map[:, 0, 1:]
    linear_map[:, 1:, 1:] = (dual_g@dd_omega.reshape(count*count, 20).T).reshape(-1, count, count)
    assert np.array_equal(linear_map, linear_map.transpose(0, 2, 1))
    # Along each line the unexpanded superpotential is a polynomial of degree
    # at most four, so the five-point derivative uses exact Gaussian integers.
    for direction in (np.arange(dim) % 3-1, np.arange(dim)**2 % 5-2, (1j)**np.arange(dim)):
        changing_rows = np.tensordot(direction[1:], tangents, axes=1)
        second_derivative = sum(weight*((dual_g+t*direction[0]*fluxes)@wedge(dz+t*changing_rows))
                                for t, weight in ((-2,-1),(-1,16),(0,-30),(1,16),(2,-1)))
        assert np.array_equal(second_derivative, 12*((linear_map@direction)@direction))
    singular = np.linalg.svd(linear_map, compute_uv=False)
    ranks = np.count_nonzero(singular > 1e-8, axis=1)

    def exact_complex_rank(matrix):
        # Realification over the rationals doubles the Gaussian-rational rank.
        real = matrix.real.astype(int)
        imag = matrix.imag.astype(int)
        assert np.array_equal(matrix, real+1j*imag)
        rows = np.block([[real, -imag], [imag, real]]).tolist()
        rank = 0
        for col in range(len(rows[0])):
            pivot = next((k for k in range(rank, len(rows)) if rows[k][col]), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            p = rows[rank][col]
            for k in range(rank+1, len(rows)):
                v = rows[k][col]
                if v:
                    common = gcd(p, v)
                    reduced = [(p//common)*x-(v//common)*y for x, y in zip(rows[k], rows[rank])]
                    divisor = gcd(*reduced) or 1
                    rows[k] = [entry//divisor for entry in reduced]
            rank += 1
        assert rank % 2 == 0
        return rank//2

    orbit_hist = Counter()
    for orbit in representatives:
        first = orbit[0]
        rank = exact_complex_rank(linear_map[first])
        assert np.all(ranks[orbit] == rank)
        norm2 = int(fluxes[first]@fluxes[first])
        orbit_hist[(norm2, rank)] += 1
    report = dict(moduli=dim,
                marked_rank_histogram=dict(sorted(Counter(ranks.tolist()).items())),
                orbits_by_norm_and_rank={str(n): {str(k): v for (m, k), v in sorted(orbit_hist.items())
                                                  if m == n} for n in range(0, 9, 2)},
                full_rank_marked=int(np.sum(ranks == dim)),
                full_rank_orbits=sum(v for (m, k), v in orbit_hist.items() if k == dim))
    return report, ranks == dim


def torus_fluxes(*, include_marked=False):
    """Even covering fluxes at the marked square O3 orientifold and tau=i."""
    triples = list(itertools.combinations(range(6), 3))
    index = {v: i for i, v in enumerate(triples)}
    signs = lambda seq: (-1)**sum(a>b for i, a in enumerate(seq) for b in seq[i+1:])
    line = np.array([1, 2, 0, 0, 2, 0, 0, 0, 0], dtype=np.int64)
    unrestricted = np.array([1], dtype=np.int64)
    for _ in range(20):
        unrestricted = np.convolve(unrestricted, line)[:9]

    components = []
    for parity in (0, 1):
        indices, orientation = [], []
        for bits in itertools.product(range(2), repeat=3):
            weight = sum(bits)
            if weight % 2 == parity:
                indices.append(index[tuple(2*j+b for j, b in enumerate(bits))])
                orientation.append((-1)**(weight//2))
        options = []
        for v in itertools.product(range(-2, 3), repeat=4):
            energy = sum(x*x for x in v)
            if energy <= 8 and sum(x*y for x,y in zip(orientation,v)) == 0:
                options.append((energy,v))
        components.append((indices, options))
    for singleton in range(6):
        indices = [index[tuple(sorted([2*j,2*j+1,singleton]))]
                   for j in range(3) if j != singleton//2]
        components.append((indices, [(2*k*k,(k,-k)) for k in range(-2,3)]))
    fluxes = []
    def extend(j, energy, v):
        if j == len(components):
            fluxes.append(v.copy())
            return
        indices, values = components[j]
        for cost, values_here in values:
            if cost+energy <= 8:
                v[indices] = values_here
                extend(j+1, energy+cost, v)
    extend(0, 0, np.zeros(20, dtype=np.int8))
    all_flux = np.array(fluxes)
    # Independent linear exterior-algebra constraints J wedge F = 0 and Omega wedge F = 0.
    tests = np.zeros((8,20), dtype=int)
    for i, form in enumerate(triples):
        for j in range(3):
            five = (2*j,2*j+1)+form
            if len(set(five)) == 5:
                missing, = set(range(6))-set(five)
                tests[missing,i] += signs(five)
        complement = tuple(k for k in range(6) if k not in form)
        if len({k//2 for k in complement}) == 3:
            coefficient = 1j**sum(k%2 for k in complement)*signs(complement+form)
            tests[6,i], tests[7,i] = int(coefficient.real), int(coefficient.imag)
    assert np.linalg.matrix_rank(tests) == 8 and not (all_flux@tests.T).any()
    def exterior_map(perm, sign):
        matrix = np.zeros((20,20), dtype=np.int8)
        for j, form in enumerate(triples):
            moved = tuple(perm[k] for k in form)
            matrix[index[tuple(sorted(moved))],j] = signs(moved)*np.prod([sign[k] for k in form])
        return matrix
    group = [exterior_map([1,0,2,3,4,5], [1,-1,1,1,1,1]),
             exterior_map([2,3,0,1,4,5], [1]*6), exterior_map([0,1,4,5,2,3], [1]*6)]
    hodge = np.zeros((20,20), dtype=np.int8)
    for j, form in enumerate(triples):
        other = tuple(k for k in range(6) if k not in form)
        hodge[index[other],j] = signs(form+other)
    np.testing.assert_array_equal(hodge@hodge, -np.eye(20,dtype=int))
    locate = {row.tobytes(): i for i,row in enumerate(all_flux)}
    def orbits(generators):
        images = np.array([[locate[row.tobytes()] for row in all_flux@m.T] for m in generators])
        unseen = set(range(len(all_flux)))
        bins = Counter()
        members = []
        while unseen:
            first = unseen.pop()
            stack = [first]
            orbit = [first]
            while stack:
                for target in images[:,stack.pop()]:
                    if target in unseen:
                        unseen.remove(target)
                        stack.append(target)
                        orbit.append(target)
            bins[int(all_flux[first]@all_flux[first])] += 1
            members.append(orbit)
        return dict(sorted(bins.items())), members
    reduced, members = orbits(group)
    assert reduced == orbits(group+[hodge])[0]
    norm2 = np.sum(all_flux.astype(int)**2,axis=1)
    primitive = np.bincount(norm2,minlength=9)
    assert len(locate) == len(fluxes) == sum(primitive)
    # Independent Burnside count over all square-lattice holomorphic isometries.
    fixed_counts = np.zeros(9,dtype=int)
    for perm in itertools.permutations(range(3)):
        for turns in itertools.product(range(4),repeat=3):
            axis, orientation = [], []
            for j,k in enumerate(turns):
                for a in (0,1):
                    axis.append(2*perm[j]+(a+k)%2)
                    orientation.append((-1)**((a+k)//2))
            rotation = exterior_map(axis, orientation)
            col = np.argmax(np.abs(rotation),axis=0)
            sign = rotation[col, np.arange(20)]
            fixed = np.all(all_flux[:,col] == all_flux*sign, axis=1)
            fixed_counts += np.bincount(norm2[fixed],minlength=9)
    np.testing.assert_array_equal(fixed_counts, [384*reduced.get(i,0) for i in range(9)])
    polarized, polarized_full = flux_mass_ranks(all_flux, members, hodge, triples, True)
    general, general_full = flux_mass_ranks(all_flux, members, hodge, triples, False)
    np.testing.assert_array_equal(polarized_full, general_full)
    if include_marked:
        return all_flux, members, hodge, triples, general_full
    return dict(bare_isd_shells=unrestricted.tolist(), raw_isd=int(sum(unrestricted)),
                primitive_shells=primitive.tolist(), marked_primitive=len(fluxes),
                reduced_shells=reduced, reduced_total=sum(reduced.values()),
                burnside_sum=fixed_counts.tolist(),
                polarized_mass_ranks=polarized, general_period_mass_ranks=general)


def sky():
    # Verify the linear relation between two phase-referenced harmonic observables.
    dim, alpha = 35, 1.13+.42j
    a = np.diag(np.sqrt(np.arange(1, dim)), 1)
    wave = expm(alpha*a.T-alpha.conjugate()*a)[:, 0]
    rho = np.outer(wave, wave.conj())
    parity = np.arange(dim) % 2
    p0, even, number = .32, .43, .25
    written = p0*rho+even*rho*(parity[:, None] == parity)+number*np.diag(np.diag(rho))
    v = [(np.trace(np.linalg.matrix_power(a,n)@written)/
          np.trace(np.linalg.matrix_power(a,n)@rho)).real for n in (1, 2)]
    inverse = expm(-alpha*a.T+alpha.conjugate()*a)
    ratio = (np.trace(a.T@a@inverse@written@inverse.conj().T)/abs(alpha)**2).real
    np.testing.assert_allclose([*v, ratio], [p0, p0+even, 2*(1-p0)], atol=2e-13)
    pg, pph = .95, .81
    eta_g, eta_ph = pg**-.5, pph**-.5
    np.testing.assert_allclose(eta_g/eta_ph, np.sqrt(pph/pg))
    # Outbound + inbound null travel, with the barrier at the photon sphere.
    epsilon = 1e-4
    solar_mass_time = 1.3271244e20 / 299792458**3
    round_trip_scale_ms = 4*30*solar_mass_time*1000
    delay = round_trip_scale_ms*(0.5-epsilon+np.log(0.5/epsilon))
    integrated_delay = round_trip_scale_ms*quad(lambda u: 1+1/u, epsilon, 0.5)[0]
    np.testing.assert_allclose(delay, integrated_delay, rtol=2e-13)
    return dict(normalized_harmonics=v, opposite_kick_energy_ratio=ratio,
                recovered_mixture=[v[0],v[1]-v[0],1-v[1]],
                optical_distance_ratio=eta_ph, flux_siren_distance_ratio=eta_g,
                two_distance_ratio=eta_g/eta_ph, echo_source_frame_ms=delay)


def interlayer_vacuum():
    """Vacuum retention through C3 and C4, plus compatible internal sections."""
    identity = np.eye(2)
    route_swap = np.array([[0., 1.], [1., 0.]])
    incoming = np.array([1., 0.])
    v = np.array([1., 1j])/np.sqrt(2)
    outer_v = np.outer(v, v.conj())
    test_vector = np.kron(v, incoming)
    kept = sent = changed = 0.
    # Two actual, individually recorded port outcomes. The pass projection
    # in the first outcome does not commute with the ordinary vacuum projection.
    for kraus, passing in ((np.diag([1, 0]), np.ones((2, 2))/2),
                           (np.diag([0, 1]), np.diag([0, 1]))):
        amplitude = kraus@v
        w = np.kron(passing, identity)+np.kron(identity-passing, route_swap)
        output = w@np.kron(amplitude, incoming)
        kept += abs(np.vdot(test_vector, output))**2
        sent += np.linalg.norm((identity-passing)@amplitude)**2
        changed += np.linalg.norm((identity-outer_v)@passing@amplitude)**2
    np.testing.assert_allclose(kept+sent+changed, 1.)

    # Two triangles sharing one endpoint. Extending the tree adds further
    # layers without adding closed paths. We fix internal modes, not histories.
    holonomies = ((identity, identity), (np.diag([1,-1]), identity),
                  (np.diag([1,-1]), np.diag([-1,1])))
    counts = {}
    for vertices in (5, 12, 32):
        modes = []
        for g, h in holonomies:
            links = [(0,1,identity),(1,2,identity),(2,0,g),
                     (0,3,identity),(3,4,identity),(4,0,h)]
            links.extend((i-1,i,identity) for i in range(5, vertices))
            mismatch = np.zeros((2*len(links), 2*vertices))
            for e, (i,j,rotation) in enumerate(links):
                mismatch[2*e:2*e+2, 2*i:2*i+2] = -rotation
                mismatch[2*e:2*e+2, 2*j:2*j+2] = identity
            direct = 2*vertices-int(np.linalg.matrix_rank(mismatch))
            common = 2-int(np.linalg.matrix_rank(np.vstack([identity-g, identity-h])))
            assert direct == common
            modes.append(direct)
        assert modes == [2,1,0]
        counts[str(vertices)] = modes
    return dict(same_vacuum_and_route=kept, changed_route=sent,
                same_route_changed_state=changed, compatible_sections=counts)


def collapse_and_gravitons():
    # A nonzero defect in the same preparation sector obstructs exact routing
    # on an open set. Rotating the basis makes the two path effects noncommuting.
    rng = np.random.default_rng(168)
    basis = np.linalg.qr(rng.normal(size=(5, 5))+1j*rng.normal(size=(5, 5)))[0]
    e = basis[:, 1]
    psi = basis[:, 0]
    b = basis@np.diag([0., .65, .08, .85, .4])@basis.conj().T
    rotated = (basis[:, 2]+basis[:, 1])/np.sqrt(2)
    a = np.eye(5)-.2*np.outer(rotated, rotated.conj())
    defect = np.eye(5)-a+b
    assert np.linalg.norm(a@b-b@a) > .01
    for delta in (1e-6, .001, .05):
        for phase in (.2, 1., 2.8):
            state = np.sqrt(1-delta)*psi+np.exp(1j*phase)*np.sqrt(delta)*e
            np.testing.assert_allclose(np.vdot(state, defect@state).real, delta*.75, atol=5e-15)
    # Compute two helicity amplitudes directly from the electric and magnetic
    # Weyl polarization tensors, without using the closed angle formula.
    mass_in, mass_core = 10., 8.
    output = []
    for cosine in (-1., -.5, 0., .5, 1.):
        sine = np.sqrt(1-cosine**2)
        n1 = np.array([0.,0.,1.])
        n2 = np.array([sine,0.,cosine])
        e1, e2 = np.array([1.,0.,0.]), np.array([cosine,0.,-sine])
        y = np.array([0.,1.,0.])
        amplitudes = []
        for h1, h2 in itertools.product((-1, 1), repeat=2):
            pol1, pol2 = (e1+1j*h1*y)/np.sqrt(2), (e2+1j*h2*y)/np.sqrt(2)
            electric1, electric2 = np.outer(pol1, pol1), np.outer(pol2, pol2)
            magnetic1 = np.cross(n1, electric1.T).T
            magnetic2 = np.cross(n2, electric2.T).T
            amplitudes.append([np.sum(electric1*electric2), np.sum(magnetic1*magnetic2)])
        modes = np.array(amplitudes)
        gram = modes.conj().T@modes
        overlap = (gram[0,1]/np.sqrt(gram[0,0]*gram[1,1])).real
        plus, minus = (1-cosine)**4, (1+cosine)**4
        np.testing.assert_allclose(overlap, (minus-plus)/(minus+plus), atol=3e-15)
        difference = mass_in**2-mass_core**2
        energy = difference/(2*mass_in+np.sqrt(4*mass_in**2-2*(1-cosine)*difference))
        momentum = energy*(n1+n2)
        np.testing.assert_allclose(2*energy+np.sqrt(mass_core**2+momentum@momentum), mass_in)
        output.append(dict(cosine=cosine, energy_per_graviton=energy, pattern_overlap=overlap,
                           rank=int(np.linalg.matrix_rank(gram, tol=1e-12))))
    return dict(largest_path_defect=float(np.linalg.eigvalsh(defect)[-1]),
                two_graviton_patterns=output)


if __name__ == "__main__":
    results = dict(geometries=matrix_geometries(), quantum_sectors=quantum_sectors(),
                   orientifold=torus_fluxes(), sky=sky(), interlayer_vacuum=interlayer_vacuum(),
                   collapse=collapse_and_gravitons())
    path = Path(__file__).resolve().parents[1]/"verification"/"cat-vacua-sky-results.json"
    path.write_text(json.dumps(results, indent=2, allow_nan=False)+"\n", encoding="utf8")
