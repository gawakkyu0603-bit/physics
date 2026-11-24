"""Flat E3 divisors and the common volume of the square O3 flux sectors."""
import itertools
import json
from collections import Counter
from math import gcd, isqrt
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from cat_tidal_crossing import integer_kernel, kahler_constraints
from cat_vacua_sky import torus_fluxes


def determinant3(m):
    a, b, c = m
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0])
            + a[2]*(b[0]*c[1]-b[1]*c[0]))


def coefficients(triples):
    # Evaluate on twice the complex tangent derivatives. All entries are
    # Gaussian integers of very small norm, exactly representable as doubles.
    hol = np.eye(6)[::2] - 1j*np.eye(6)[1::2]
    result = np.zeros((20, 3, 3), dtype=complex)
    for normal in range(3):
        for anti in range(3):
            tangents = np.array((hol[(normal+1)%3], hol[(normal+2)%3], hol[anti].conj()))
            for k, triple in enumerate(triples):
                result[k, normal, anti] = determinant3(tangents[:, triple])
    return result


def canonical_normal(vector):
    """A primitive Gaussian normal, unique up to units of Z[i]."""
    values = np.rint(np.real(vector)).astype(int) + 1j*np.rint(np.imag(vector)).astype(int)
    assert np.array_equal(values, vector)
    factor = 0j
    for entry in values:
        a, b = factor, complex(entry)
        while b:
            quotient = a/b
            remainder = a - complex(round(quotient.real), round(quotient.imag))*b
            assert abs(remainder) < abs(b)
            a, b = b, remainder
        factor = a
    assert factor
    values = (values*factor.conjugate())/round(abs(factor)**2)
    assert np.array_equal(np.rint(values.real)+1j*np.rint(values.imag), values)
    return min(tuple((int(x.real), int(x.imag)) for x in values*unit) for unit in (1, -1, 1j, -1j))


def normal_vector(key):
    return np.array([complex(a,b) for a,b in key])


def restriction(normal, triples):
    # The four columns span the true rational tangent lattice over Q. Testing
    # a finite-index basis suffices for vanishing of a class on this cover.
    rows = np.empty((2, 6), dtype=np.int64)
    rows[0, ::2], rows[0, 1::2] = normal.real, -normal.imag
    rows[1, ::2], rows[1, 1::2] = normal.imag, normal.real
    tangent = integer_kernel(rows)
    return np.array([[determinant3(tangent[list(form)][:, axes]) for form in triples]
                     for axes in itertools.combinations(range(4), 3)], dtype=np.int64)


def rational_axes(s):
    # Use the monic integral characteristic polynomial of the Hermitian
    # matrix S* S. A rational eigenline has a real rational eigenvalue.
    re, im = s.real.astype(np.int64), s.imag.astype(np.int64)
    divisor = gcd(*re.flatten().tolist(), *im.flatten().tolist())
    re, im = re//divisor, im//divisor
    s = re+1j*im
    gram = s.conj().T@s
    trace = int(np.trace(gram).real)
    second = sum(int((gram[i,i]*gram[j,j]-gram[i,j]*gram[j,i]).real)
                 for i,j in itertools.combinations(range(3),2))
    determinant = determinant3(s)
    constant = int(determinant.real)**2+int(determinant.imag)**2
    roots = {}
    obstructions = {}
    axes = set()
    infinite = False
    for mu in range(trace+1):
        if ((mu-trace)*mu+second)*mu != constant:
            continue
        multiplicity = 1 + int(3*mu**2-2*trace*mu+second == 0)
        if multiplicity == 2 and 3*mu == trace:
            multiplicity = 3
        roots[mu] = multiplicity
        norm = next(((a,isqrt(mu-a*a)) for a in range(isqrt(mu)+1)
                     if isqrt(mu-a*a)**2 == mu-a*a), None)
        if norm is None:
            # A prime that is 3 mod 4 has even valuation in any nonzero
            # norm from Q(i), including after denominators are allowed.
            for prime in range(3,mu+1,4):
                if any(prime % d == 0 for d in range(2,isqrt(prime)+1)):
                    continue
                exponent, residual = 0, mu
                while residual % prime == 0:
                    exponent += 1
                    residual //= prime
                if exponent % 2:
                    obstructions[mu] = [prime,exponent]
                    break
            assert mu in obstructions
            continue
        a,b = norm
        identity = np.eye(3,dtype=np.int64)
        real_form = np.block([[re-a*identity, -im-b*identity],
                              [im-b*identity, re+a*identity]])
        basis = integer_kernel(real_form)
        expected = multiplicity if mu else 2*multiplicity
        assert basis.shape == (6,expected)
        columns = basis[:3]+1j*basis[3:]
        assert np.array_equal(s@columns, (a+1j*b)*columns.conj())
        infinite |= multiplicity >= 2
        seeds = list(columns.T)
        for left,right in itertools.combinations(columns.T,2):
            seeds.extend((left+right, left+2*right))
        for vector in seeds:
            if vector.any():
                axes.add(canonical_normal(vector))
    return (trace, second, constant), roots, obstructions, axes, infinite


def small_normals(max_norm):
    cap = isqrt(max_norm)
    entries = [complex(a,b) for a in range(-cap,cap+1) for b in range(-cap,cap+1)
               if a*a+b*b <= max_norm]
    return sorted({canonical_normal(np.array(v)) for v in itertools.product(entries,repeat=3)
                   if 0 < sum(int(x.real)**2+int(x.imag)**2 for x in v) <= max_norm})


def divisor_census():
    fluxes, orbits, star, triples, fixed = torus_fluxes(include_marked=True)
    dual = fluxes.astype(np.int64)@star.T
    tensor = coefficients(triples)
    linear = kahler_constraints(star,triples)
    short = small_normals(5)
    short_vectors = np.array([normal_vector(key) for key in short])
    direct = dict((key,restriction(vector,triples)) for key,vector in zip(short,short_vectors))
    rows, types, marked = [], Counter(), Counter()
    for orbit in orbits:
        j = orbit[0]
        if not fixed[j]:
            continue
        f,h = fluxes[j].astype(np.int64), dual[j]
        s = np.tensordot(f-1j*h,tensor,axes=1)
        assert s.any() and np.array_equal(s,s.T) and np.abs(s).max()<64
        assert np.array_equal(s,s.real.round()+1j*s.imag.round())
        cubic, roots, obstructions, axes, infinite = rational_axes(s)
        passes = set()
        for key, n in zip(short, short_vectors):
            rs = s@n
            condition = not np.cross(rs,n.conj()).any()
            restrict_f, restrict_h = direct[key]@f, direct[key]@h
            assert (not restrict_h.any()) == condition == (not restrict_f.any())
            if condition:
                passes.add(key)
        if infinite:
            axes |= passes
        else:
            assert passes == {k for k in axes if sum(a*a+b*b for a,b in k) <= 5}
        for key in axes:
            target = direct[key] if key in direct else restriction(normal_vector(key),triples)
            assert not (target@f).any() and not (target@h).any()
        winding = sorted({sum(a*a+b*b for a,b in key) for key in axes})
        if not infinite and len(axes)>1:
            vectors = [normal_vector(key) for key in axes]
            assert all(np.vdot(u,v)==0 for u,v in itertools.combinations(vectors,2))
        category = "infinite" if infinite else str(len(axes))
        types[category] += 1
        marked[category] += len(orbit)
        rows.append(dict(flux=f.tolist(),orbit_size=len(orbit),d3_brane_budget=16-2*int(f@f),
                         integral_cubic=list(cubic),rational_roots=roots,non_norm_roots=obstructions,
                         normal_lines=category,
                         actions_in_units_of_coordinate_divisor=winding,
                         actions_exhaustive=not infinite, tested_norm_max=5,
                         example_normals=sorted(axes)[:8]))
    assert len(rows)==49 and sum(marked.values())==12048
    example = np.array(rows[0]["flux"],dtype=np.int64)
    first_equations = linear(example[None,:])[0]
    # Kähler forms: diagonal components, then real/imaginary parts in each
    # plane. The real off-diagonal metric corresponds to the mixed dx/dy form.
    surviving_columns = [i for i in range(9) if not first_equations[:,i].any()]
    assert len(surviving_columns)==4 and integer_kernel(first_equations).shape[1]==4
    example_class = [np.eye(3,dtype=int)[i] for i in range(3)]
    example_class += [example_class[0]+example_class[1],example_class[0]-example_class[1]]
    for n in example_class:
        check = restriction(n.astype(complex),triples)
        assert not (check@example).any() and not (check@(star@example)).any()
    return dict(orbits=dict(types),marked_fluxes=dict(marked),directly_tested_normals=len(short),
                example_kahler_columns=surviving_columns,
                no_second_flat_slope=sum(not r['normal_lines']=="infinite" and
                                         len(r['actions_in_units_of_coordinate_divisor'])<2 for r in rows),
                examples=rows)


def five_divisor_minimum(tau):
    # Adapted four-cycle coordinates are T11,T22,T33,T12. Compare the
    # canonical supergravity masses with the full eight-real-variable Hessian.
    a=2*np.pi
    s=a*tau
    charges=np.array([[1,0,0,0],[0,1,0,0],[0,0,1,0],[1,1,0,2],[1,1,0,-2]])
    background=np.array([tau,tau,tau,0.])
    terms=np.array([-2-2*s,-2-2*s,1.,(3+2*s)/2,(3+2*s)/2])
    w=terms.sum()
    # Common rescaling of W cancels from the mass ratios. It may be taken
    # small enough for a heavy-moduli truncation, subject to microscopic data.
    matrix_k=np.diag([1,1,1,2])/(4*tau**2)
    first_k=np.array([-1.,-1.,-1.,0.])/(2*tau)
    ww=a*a*charges.T@(terms[:,None]*charges)
    inv_sqrt=np.diag(1/np.sqrt(np.diag(matrix_k)))
    np.testing.assert_allclose(-a*(terms@charges)+first_k*w,0,atol=3e-13)
    zz=inv_sqrt@(ww/w+matrix_k-np.outer(first_k,first_k))@inv_sqrt
    singular=np.abs(np.linalg.eigvalsh(zz))
    even=np.array([[1+8*s+4*s*s,np.sqrt(2)],[np.sqrt(2),2*s]])
    predicted=np.r_[np.linalg.eigvalsh(even),(1+2*s)**2,abs(1-4*s*(3+2*s))]
    np.testing.assert_allclose(sorted(singular),sorted(predicted),rtol=2e-13)
    masses=sorted(np.r_[singular**2-2-singular, singular**2-2+singular])

    elementary=np.zeros((4,3,3))
    elementary[:3]=np.array([np.diag(row) for row in np.eye(3)])
    elementary[3,0,1]=elementary[3,1,0]=1
    def potential(displacement):
        u=displacement[:4]+1j*displacement[4:]
        y=np.tensordot(background+u.real,elementary,axes=1)
        det=np.linalg.det(y)
        inverse=np.linalg.inv(y)
        k_i=-np.einsum("ij,aji->a",inverse,elementary)/2
        product=inverse[None,:,:]@elementary
        metric=np.einsum("aij,bji->ab",product,product)/4
        vals=terms*np.exp(-a*(charges@u))
        total=vals.sum()
        dw=-a*(vals@charges)+k_i*total
        return (np.vdot(dw,np.linalg.solve(metric,dw)).real-3*abs(total)**2)/det
    h=1.5e-4/a
    axis=np.eye(8)*h
    center=potential(np.zeros(8))
    difference=np.zeros((8,8))
    for i in range(8):
        difference[i,i]=(potential(axis[i])+potential(-axis[i])-2*center)/h**2
        for j in range(i):
            value=(potential(axis[i]+axis[j])-potential(axis[i]-axis[j])
                   -potential(-axis[i]+axis[j])+potential(-axis[i]-axis[j]))/(4*h*h)
            difference[i,j]=difference[j,i]=value
    canon=np.tile(np.diag(inv_sqrt)/np.sqrt(2),2)
    measured=np.linalg.eigvalsh(canon[:,None]*difference*canon/(-center/3))
    np.testing.assert_allclose(measured,masses,rtol=3e-5)
    assert min(masses)>0 and center<0
    error=np.max(np.abs(measured-masses)/masses)
    assert error < 1.e-6
    return dict(tau=tau,coordinate_action=s,
                prefactors_over_third=[-2-2*s,-2-2*s,1.,(3+2*s)*np.exp(s)/2],
                scalar_masses_over_gravitino_mass_squared=masses,
                finite_difference_relative_error_below_one_part_per_million=bool(error < 1.e-6))


def common_volume():
    # An effective one-complex-modulus diagnostic in reduced Planck units.
    # The two prefactors are examples, not microscopic CAT coefficients.
    a,b=2*np.pi,4*np.pi
    cases=[]
    for ratio in (1.1,10.,1.e3,1.e6):
        def equation(t):
            return (b-a)*t+np.log((2*a*t+3)/(2*b*t+3))-np.log(ratio)
        tau=brentq(equation,0,20,xtol=2e-14)
        z=2+2*(a+b)*tau+4*a*b*tau*tau/3
        def potential(t,ax):
            first=np.exp(-a*(t+1j*ax))
            second=-ratio*np.exp(-b*(t+1j*ax))
            w=first+second
            deriv=-a*first-b*second-3*w/(2*t)
            return ((4*t*t/3)*abs(deriv)**2-3*abs(w)**2)/(2*t)**3
        v0=potential(tau,0)
        h=1e-4*min(tau,1/b)
        canon=2*tau**2/3
        hessian=np.array([(potential(tau+h,0)-2*v0+potential(tau-h,0))/h**2,
                          (potential(tau,h)-2*v0+potential(tau,-h))/h**2])*canon/(-v0/3)
        np.testing.assert_allclose(sorted(hessian),[z*z-2-z,z*z-2+z],rtol=5e-5)
        cases.append(dict(prefactor_ratio=ratio,tau=tau,volume=tau**1.5,action=a*tau,
                          partner_scalar_masses_over_gravitino_mass_squared=[z*z-2-z,z*z-2+z]))
    # Einstein frame, six equal radii and a fixed ten-dimensional rest mass.
    alpha2=9/24
    return dict(scalar_charge_squared=alpha2,yukawa_strength=2*alpha2,
                ppn_gamma=(1-2*alpha2)/(1+2*alpha2),racetrack_examples=cases,
                two_slope_minimum_ratios={str(t): np.exp(2*np.pi*t)*(4*np.pi*t+3)/(8*np.pi*t+3)
                                          for t in (1,2,5,10)},
                five_divisor_examples=[five_divisor_minimum(t) for t in (1.,2.,5.)])


if __name__=="__main__":
    output=dict(divisors=divisor_census(),effective=common_volume())
    path=Path(__file__).resolve().parents[1]/"verification"/"cat-volume-sectors-results.json"
    path.write_text(json.dumps(output,indent=2,allow_nan=False)+"\n",encoding="utf8")
