"""Neutral E3 modes, scalar forces and a microscopic radius test on the O.3 torus."""
import itertools
import json
from collections import Counter
from pathlib import Path

import numpy as np
from scipy import constants
from scipy.linalg import null_space
from scipy.optimize import brentq, root

from cat_vacua_sky import torus_fluxes
from cat_volume_sectors import coefficients, normal_vector, rational_axes, small_normals


def heavy_response(f, star, triples):
    """Compute the propagator in the explicit period coordinates of Appendix O."""
    triple = np.array(triples).T
    identity = np.eye(3)
    def flux_superpotential(displacement):
        periods = 1j*identity+displacement[1:].reshape(3,3)
        forms = np.empty((3,6),dtype=complex)
        forms[:,::2], forms[:,1::2] = identity, periods
        a,b,c = forms[:,triple]
        omega = (a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])
                 +a[2]*(b[0]*c[1]-b[1]*c[0]))
        return (star@f+(1j+displacement[0])*f)@omega
    def second(v):
        return sum(weight*flux_superpotential(t*v) for t,weight in
                   ((-2,-1),(-1,16),(0,-30),(1,16),(2,-1)))/12
    axes = np.eye(10)
    diagonal = [second(v) for v in axes]
    h = np.array([[(second(a+b)-diagonal[i]-diagonal[j])/2 for j,b in enumerate(axes)]
                  for i,a in enumerate(axes)])
    inverse = np.linalg.inv(h)
    # Recover an exact Gaussian-rational inverse and certify it by multiplication.
    for denom in range(1,4097):
        scaled = inverse*denom
        num = np.round(scaled.real)+1j*np.round(scaled.imag)
        if np.array_equal(h@num,denom*np.eye(10)):
            break
    else:
        raise AssertionError("No certified inverse within the denominator bound")
    labels = ["axiodilaton"]+[f"Z{i+1}{j+1}" for i,j in itertools.product(range(3),repeat=2)]
    diag_inv = [[int(a.real),int(a.imag)] for a in np.diag(num)]
    return dict(coordinates=labels, denominator=denom, diagonal_complex_numerators=diag_inv,
                real_numerators=num.real.astype(int).tolist(), imag_numerators=num.imag.astype(int).tolist())


def point_group(s):
    # All unitary Gaussian lattice automorphisms are monomial. Here the
    # dilaton is held fixed; translations and combined S dualities are omitted.
    normals = np.array([[1,0,0],[0,1,0],[0,0,1],[1,1,0],[1,-1,0]],dtype=complex)
    images = [set() for n in normals]
    order = 0
    for perm in itertools.permutations(range(3)):
        for signs in itertools.product((1,1j,-1,-1j), repeat=3):
            rotation = np.eye(3)[list(perm)]@np.diag(signs)
            determinant = np.linalg.det(rotation)
            if not np.array_equal(rotation@s@rotation.T,determinant*s):
                continue
            assert determinant == 1
            order += 1
            for i,n in enumerate(normals):
                transformed = rotation.T@n
                matches = [j for j,m in enumerate(normals) if not np.any(np.cross(m,transformed))]
                assert len(matches) == 1
                images[i].add(matches[0])
    assert order == 8 and [len(g) for g in images] == [2,2,1,2,2]
    return dict(linear_holomorphic_flux_isometries=order, action_on_five_normals=[sorted(g) for g in images])


def flux_tests():
    fluxes, orbits, star, triples, fixed = torus_fluxes(include_marked=True)
    basis = coefficients(triples)
    normals = [normal_vector(n) for n in small_normals(5)]
    bits = np.array(list(itertools.product((0, 1), repeat=6)))
    two_torsion = bits[:, ::2] + 1j*bits[:, 1::2]
    counts, infinite_spectra, mobile_budget = Counter(), Counter(), Counter()
    first = None
    for orbit in orbits:
        j = orbit[0]
        if not fixed[j]:
            continue
        f = fluxes[j].astype(int)
        s = np.tensordot(f-1j*(star@f), basis, axes=1)
        cubic, roots, _, _, infinite = rational_axes(s)
        assert cubic[-1] > 0 and np.array_equal(s, s.T)
        multiplicities = sorted(np.unique(np.round(np.linalg.eigvalsh(s.conj().T@s), 7),
                                          return_counts=True)[1])
        counts['kahler_dimension_'+str(sum(int(m*(m+1)//2) for m in multiplicities))] += 1
        if infinite:
            spectrum = tuple(mu for mu, multiplicity in roots.items() for _ in range(multiplicity))
            assert len(spectrum) == 3 and len(set(spectrum)) == 2
            infinite_spectra[','.join(map(str, spectrum))] += 1
            mobile_budget[str(16-2*int(f@f))] += 1
        eligible = []
        for n in normals:
            if np.any(np.cross(s@n, n.conj())):
                continue
            frame = np.column_stack((null_space(n.conj()[None, :]), n/np.linalg.norm(n)))
            adapted = frame.T@s@frame
            np.testing.assert_allclose(adapted[:2, 2], 0., atol=4e-13)
            tangent = adapted[:2, :2]
            normal = adapted[2, 2]
            four_modes = np.linalg.svd(tangent, compute_uv=False)
            assert min(four_modes) > 1e-5 and abs(normal) > 1e-5
            np.testing.assert_allclose(np.prod(four_modes)*abs(normal), abs(np.linalg.det(s)))
            # Doubled coordinates of the image of all fixed points on E[2].
            image = two_torsion@n
            translates = Counter(zip(image.real.astype(int)%2, image.imag.astype(int)%2))
            assert sorted(translates.values()) == [16]*4
            eligible.append(n)
        counts['orbits'] += 1
        counts['tested_lines'] += len(normals)
        counts['eligible_short_lines'] += len(eligible)
        counts['orbits_with_short_line'] += bool(eligible)
        if first is None:
            short_actions = Counter(round(np.vdot(n,n).real) for n in eligible)
            assert short_actions[1] == 3 and short_actions[2] == 2
            first = dict(flux=f.tolist(), short_actions=dict(sorted(short_actions.items())),
                         neutral_lift_product_in_flux_basis=round(abs(np.linalg.det(s)), 9),
                         mobile_D3_budget=16-2*int(f@f), heavy_inverse=heavy_response(f,star,triples),
                         square_lattice_point_group=point_group(s))
    assert counts['orbits'] == 49 and sum(infinite_spectra.values()) == 8
    return dict(counts=dict(counts), infinite_spectra=dict(infinite_spectra),
                mobile_D3_budget_of_infinite_families=dict(mobile_budget),
                first_sector=first, fixed_points_per_invariant_translate=16,
                neutral_modes=dict(invariant_before=8, invariant_after=2,
                                   exchanged_before=16, exchanged_after=10))


def curvature():
    # The determinant along z=t A gives K=-log det(1-|t|^2 A A†).
    # Its second coefficient fixes the sectional curvature in normal coordinates.
    cases = [np.eye(3), np.diag([1,0,0]),
             np.array([[1+1j,2j,0],[2j,-1,0],[0,0,2-1j]]), np.diag([1j,1,-2j])]
    result = []
    for tangent in cases:
        gram = tangent@tangent.conj().T
        first = np.trace(gram).real
        normed = gram/first
        section = 2*np.trace(normed@normed).real
        # Polynomial interpolation of the actual cubic determinant.
        u = np.array([0., .125, .25, .375])
        values = [np.linalg.det(np.eye(3)-t*normed).real for t in u]
        polynomial = np.linalg.solve(np.vander(u,4,increasing=True),values)
        np.testing.assert_allclose(2*(polynomial[1]**2-2*polynomial[2]), section, atol=3e-13)
        assert section >= 2/3-5e-15
        result.append(float(section))
    return result


def force_tests():
    mpc = 1e6*constants.parsec
    hbar_c = constants.hbar*constants.c/constants.electron_volt  # eV m
    h_lambda = constants.hbar/constants.electron_volt * 67400/mpc*np.sqrt(.685)
    rows = []
    for tau in (1., 2., 5.):
        s = 2*np.pi*tau
        diag = 1+8*s+4*s**2
        matrix = np.array([[diag,np.sqrt(2)], [np.sqrt(2),2*s]])
        eigen, vectors = np.linalg.eigh(matrix)
        alpha = -np.array([np.sqrt(2),1])/(2*np.sqrt(2))
        strength = 2*(alpha@vectors)**2
        k = diag-eigen[0]
        np.testing.assert_allclose(strength[0], (k-2)**2/(4*(k*k+2)))
        np.testing.assert_allclose(strength.sum(), .75)
        masses = np.sqrt(eigen**2+eigen-2)
        assert strength[0] > .2 and masses[0] < 2*s+.5
        rows.append(dict(tau=tau, strengths=strength.tolist(), mass_over_gravitino=masses.tolist(),
                         minimum_compton_Mpc=(hbar_c/(masses*h_lambda*mpc)).tolist()))
    gamma_lower = 1+(2.1-1.96*2.3)*1e-5
    beta_max = (1-gamma_lower)/(1+gamma_lower)
    alpha_max = np.sqrt(beta_max/2)
    # The mean warp offset may be shifted into c. Test its invariant combinations.
    c, mean = 3., 2.
    warp = []
    for local in (2.,12.,4997.):
        log_mass = lambda v: -.5*np.log(v+mean)-.25*np.log(v+local)
        dc = 1e-4
        alpha_fd = np.sqrt(2/3)*(c+mean)*(log_mass(c+dc)-log_mass(c-dc))/(2*dc)
        alpha = -np.sqrt(2/3)*(.5+(c+mean)/(4*(c+local)))
        np.testing.assert_allclose(alpha_fd, alpha, rtol=2e-9)
        warp.append(dict(warp_ratio=(c+mean)/(c+local), alpha=alpha, beta=2*alpha**2))
    # A stretched F1 has one external and one internal world-sheet direction.
    profile = np.array([1.,3.,10.,40.])
    lengths = np.array([.13,.21,.39,.27])
    def string_mass(v):
        clock = (v+mean)**(-.5)*(v+profile)**(-.25)
        ruler = (v+profile)**.25
        return lengths@(clock*ruler)
    np.testing.assert_allclose(string_mass(c),sum(lengths)/np.sqrt(c+mean))
    string_alpha = np.sqrt(2/3)*(c+mean)*(np.log(string_mass(c+dc))-np.log(string_mass(c-dc)))/(2*dc)
    np.testing.assert_allclose(string_alpha,-1/np.sqrt(6),rtol=2e-9)
    # An equal-weight three-cycle with flux-independent embedding and two warp offsets.
    delta = np.array([2.,-1.])
    w0 = .5  # derivative vanishes: 2/sqrt(2) = 1/sqrt(1/2).
    mass = lambda w: np.sqrt(1+w*delta).mean()
    slope = np.mean(delta/(2*np.sqrt(1+w0*delta)))
    second = -np.mean(delta**2/(4*(1+w0*delta)**1.5))
    width = 1e-4
    np.testing.assert_allclose(slope,0.,atol=1e-14)
    np.testing.assert_allclose((mass(w0+width)+mass(w0-width)-2*mass(w0))/width**2,
                               second,rtol=3e-7)
    return dict(localized_five_term=rows, H_Lambda_eV=h_lambda, one_AU_mass_eV=hbar_c/constants.au,
                tau_necessary_for_sub_AU_if_small_AdS=(hbar_c/(constants.au*h_lambda)-.5)/(4*np.pi),
                cassini_approx_95pct=dict(gamma_lower=gamma_lower, alpha_upper=alpha_max,
                                           coupled_mass_fraction_upper_deep_warp=np.sqrt(6)*alpha_max),
                point_warp_examples=warp, stretched_string_beta=2*string_alpha**2,
                wrapped_D3_maximum_second_derivative=second)


def quadratic_matching():
    # Complete linear and quadratic polynomial in the coordinate instantons, with
    # the two additional primitive plane directions. No complex conjugation in W.
    a = 2*np.pi
    charges = np.array([[1,0,0,0],[0,1,0,0],[0,0,1,0],
                        [1,1,0,2],[1,1,0,-2],[0,0,2,0]])
    contributions = np.array([-2.,-2.,4.,1.,1.,-2.])
    np.testing.assert_allclose(contributions.sum(),0.)
    np.testing.assert_allclose(contributions@charges,0.)
    hessian = charges.T@(contributions[:,None]*charges)
    metric_norm = np.diag([1.,1.,1.,1/np.sqrt(2)])
    mass_units = np.linalg.svd(metric_norm@hessian@metric_norm,compute_uv=False)
    np.testing.assert_allclose(sorted(mass_units),[2.,2.,4.,4.])
    # Differentiate the full holomorphic first derivative independently.
    def gradient(q):
        return -a*((contributions*np.exp(-a*(charges@q)))@charges)
    basis = np.eye(4)*1e-6
    sampled = np.column_stack([(gradient(q)-gradient(-q))/(2e-6*a*a) for q in basis])
    np.testing.assert_allclose(sampled,hessian,atol=5e-10)
    # Test the matrix criterion also at unequal sizes with complex phases and mixed pairs.
    x = np.array([.12+.03j,.09-.008j,.08+.01j])
    matrix = np.array([[1+.4j,.6j,.5],[.6j,-.8+.3j,.4j],[.5,.4j,0.]],dtype=complex)
    matrix[2,2] = -(x@matrix@x)/x[2]**2
    linear = -2*matrix@x
    def inspect(m):
        point = -.5*np.linalg.solve(m,linear)
        return point, linear@point+point@m@point, linear@np.linalg.solve(m,linear)
    point, w, invariant = inspect(matrix)
    np.testing.assert_allclose(point,x)
    np.testing.assert_allclose([w,invariant],0.,atol=1e-14)
    shifted = matrix.copy()
    shifted[2,2] += .05
    _, off_w, off_invariant = inspect(shifted)
    assert abs(off_w) > 1e-5
    np.testing.assert_allclose(off_w,-off_invariant/4)
    # Six-term square example: compare the force to a specified physical length.
    reduced_planck_eV = np.sqrt(constants.hbar*constants.c**5/(8*np.pi*constants.G))/constants.electron_volt
    micron_mass = constants.hbar*constants.c/(1e-6*constants.electron_volt)
    mass_from_b = lambda tau: 8*a*a*reduced_planck_eV*np.sqrt(tau)*np.exp(-2*a*tau)
    threshold_tau = brentq(lambda tau: np.log(mass_from_b(tau)/micron_mass),4.,8.)
    # Vary the actual double-wrapping coefficient and let the fields relax.
    # Real coefficients preserve the CP-even slice; all imaginary F-terms vanish.
    tau = 5.
    epsilon = 1e-5
    shifted_terms = contributions.copy()
    shifted_terms[-1] *= 1+epsilon
    def f_terms(delta):
        y1,y2,y3,yx = np.array([tau,tau,tau,0])+delta
        det = y1*y2-yx**2
        k = -.5*np.array([y2/det,y1/det,1/y3,-2*yx/det])
        terms = shifted_terms*np.exp(-a*(charges@delta))
        return -a*terms@charges+k*terms.sum()
    solution = root(f_terms,np.zeros(4),tol=1e-11)
    assert np.max(abs(f_terms(solution.x))) < 1e-12
    y1,y2,y3,yx = np.array([tau,tau,tau,0])+solution.x
    w_new = shifted_terms@np.exp(-a*(charges@solution.x))
    gravitino_in_units = abs(w_new)/np.sqrt((y1*y2-yx**2)*y3)
    ratio = gravitino_in_units/(8*a*a*np.sqrt(tau))
    np.testing.assert_allclose(ratio,epsilon/(4*(a*tau)**2),rtol=5e-5)
    h_lambda = constants.hbar/constants.electron_volt*67400/(1e6*constants.parsec)*np.sqrt(.685)
    return dict(hessian_log_coordinates=hessian.tolist(), hessian_determinant=round(np.linalg.det(hessian)),
                fermion_masses_in_common_units=sorted(mass_units.tolist()),
                square_scalar_strengths_by_increasing_mass=[.5,.25],
                off_square_verified=True, off_square_shifted_abs_W=abs(off_w),
                threshold_eV_for_one_micron=micron_mass,
                tau_upper_for_one_micron_if_abs_Bhat_at_most_one=threshold_tau,
                square_radius_upper_string_units_same_assumption=threshold_tau**.25,
                tau5_required_matrix_over_linear_norm=np.exp(5*a)/(2*np.sqrt(3)),
                tau5_linearized_double_coefficient_tolerance_at_micron=4*(a*tau)**2*h_lambda/micron_mass,
                perturbed_coefficient=dict(epsilon=epsilon, adjusted_gravitino_over_original_light_mass=ratio),
                minimum_weight_times_sqrt_tau_for_one_micron=micron_mass/(8*a*a*reduced_planck_eV))


def matrix_scale():
    """Test the induced gravity term and one axial deformation of fuzzy S²."""
    rows = []
    for rank in (2,3,5,8):
        spin = (rank-1)/2
        z = np.arange(-spin,spin+1)
        up = np.diag(np.sqrt((spin-z[:-1])*(spin+z[:-1]+1)),-1)
        generators = [(up+up.T)/2,(up-up.T)/(2j),np.diag(z)]
        eye = np.eye(rank)
        ad = lambda m: np.kron(m,eye)-np.kron(eye,m.T)
        modes = np.array([(l*(l+1),k*k) for l in range(1,rank) for k in range(-l,l+1)])
        total, azimuthal = modes.T
        def shape(u):
            weights = np.exp(np.array([u,u,-2*u]))
            axes = [r*j for r,j in zip(weights,generators)]
            laplace = sum(ad(j)@ad(j) for j in axes)
            flux = [1j*(j@k-k@j) for j,k in itertools.combinations(axes,2)]
            flux_square = 2*sum(ad(b)@ad(b) for b in flux)
            vals, vec = np.linalg.eigh(laplace)
            positive = vals>1e-7
            inv = (vec[:,positive]/vals[positive])@vec[:,positive].conj().T
            ratio = np.trace(inv@flux_square).real
            mu2 = np.exp(2*u)*(total-azimuthal)+np.exp(-4*u)*azimuthal
            c2 = 2*(np.exp(-2*u)*(total-azimuthal)+np.exp(4*u)*azimuthal)
            np.testing.assert_allclose(sorted(vals[positive]),sorted(mu2),rtol=1e-11)
            np.testing.assert_allclose(ratio,sum(c2/mu2),rtol=1e-11)
            tree = 2*sum(np.trace(b@b).real for b in flux)
            return ratio/(2*(rank**2-1)),tree/(rank*(rank**2-1)/2)
        def minimum(u):
            a,b = shape(u)
            return -a*a/(4*b)
        h = .0003
        curv = (minimum(h)-2*minimum(0)+minimum(-h))/h**2
        ratio_second = 4*np.mean((2-6*azimuthal/total)**2)
        signed_shape_mass = -(2*ratio_second-8)/4
        np.testing.assert_allclose(curv,signed_shape_mass,rtol=4e-6)
        assert signed_shape_mass <= -2+3e-13
        c_k2 = np.pi**2*(rank**2-1)/4
        # m_K and the measure dilation rho vary independently.
        for m,rho in ((.75,2.),(3.,.5),(2.,3.)):
            g_n = np.pi**3/(2*c_k2*(m/rho)**2)
            np.testing.assert_allclose(g_n*total*(m/rho)**2,2*np.pi*total/(rank**2-1))
        angles = np.array([.21,1.3,-.83])
        rotating = [f(theta)*j for j,theta in zip(generators,angles) for f in (np.cos,np.sin)]
        velocities = [mult*f(theta)*np.sqrt(2)*j for j,theta in zip(generators,angles)
                      for mult,f in ((-1,np.sin),(1,np.cos))]
        np.testing.assert_allclose(sum(x@v-v@x for x,v in zip(rotating,velocities)),0.,atol=3e-14)
        transverse = sum(ad(x)@ad(x) for x in rotating)
        np.testing.assert_allclose(np.linalg.eigvalsh(transverse),sorted([0,*total]),atol=1e-12)
        rows.append(dict(rank=rank, c_k_squared=c_k2, round_light_Gm2=4*np.pi/(rank**2-1),
                         normalized_reduced_shape_curvature=signed_shape_mass))
    # Fixed three target-plane charges in the C1 clock reduction, I=1.
    target_q = np.sqrt(2.)
    def energy(r):
        return .5*(sum((target_q/r)**2)+sum((r[i]*r[j])**2 for i,j in itertools.combinations(range(3),2)))
    r0 = np.ones(3)
    h = .0001
    vectors = np.eye(3)*h
    hessian = np.array([[(energy(r0+i+j)-energy(r0+i-j)-energy(r0-i+j)+energy(r0-i-j))/(4*h*h)
                         for i in vectors] for j in vectors])
    np.testing.assert_allclose(np.linalg.eigvalsh(hessian),[6,6,12],rtol=2e-7)
    # First-order Hamilton equations for all three local radii and phases. Project
    # nothing out before computing eigenvalues. Here r=1 and k is a spatial momentum.
    eye3, zero = np.eye(3),np.zeros((3,3))
    axial_mass = 2*(np.ones((3,3))-eye3)
    for k2 in (0.125,.875,1.75,2.3,7.):
        flow = np.block([[zero,zero,eye3,zero],[zero,zero,zero,eye3],
                         [-k2*eye3-axial_mass,zero,zero,2*np.sqrt(2)*eye3],
                         [zero,-k2*eye3,-2*np.sqrt(2)*eye3,zero]])
        values = -np.linalg.eigvals(flow)**2
        signs = np.array([-1,1])
        shape_modes = k2+3+signs*np.sqrt(9+8*k2)
        volume_modes = k2+6+signs*np.sqrt(36+8*k2)
        np.testing.assert_allclose(sorted(values.real),np.repeat(sorted([*volume_modes,*shape_modes,*shape_modes]),2),
                                   atol=2e-12)
        np.testing.assert_allclose(values.imag,0.,atol=2e-12)
        assert (min(shape_modes)<0) == (k2<2)
    micron_mass = constants.hbar*constants.c/(1e-6*constants.electron_volt)
    return dict(basic_static=rows, rotating_three_radius_mass_squared_over_r_squared=[6,6,12],
                rotating_frequency_over_first_transverse_frequency=1.,
                spatial_rotator=dict(common_static_mass_over_first_KK=np.sqrt(2.),
                                     shape_growth_peak_k_squared_over_r_squared=7/8,
                                     max_growth_rate_over_first_KK=.25,
                                     minimum_first_KK_eV_for_common_submicron=micron_mass/np.sqrt(2.),
                                     maximum_efold_seconds_if_common_submicron=4*np.sqrt(2)*1e-6/constants.c),
                round_l1_shape_log_derivative_k0=1.,round_l1_shape_log_derivative_k1=-.5)


if __name__ == "__main__":
    result = dict(neutral=flux_tests(), curvature_checks=curvature(),
                  matter=force_tests(), matching=quadratic_matching(), matrix=matrix_scale())
    target = Path(__file__).resolve().parents[1]/"verification"/"cat-radius-matter-results.json"
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
