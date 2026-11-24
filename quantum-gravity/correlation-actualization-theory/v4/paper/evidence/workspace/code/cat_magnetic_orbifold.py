"""Finite magnetic translations, orbital stability and the external spin response."""
import json
from functools import lru_cache
from math import gcd
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.linalg import block_diag, eigvalsh, null_space, svdvals
from scipy.optimize import brentq
from scipy.special import xlogy


def spectrum(order, nodes, gauge=1.0, flux=1):
    """Static local propagators on diagonal scalar backgrounds in the projected theory."""
    twist = np.exp(-2j * np.pi * flux / order)
    cycle = np.exp(2j * np.pi / 3)
    h = np.sqrt(2 / 3) * gauge
    yukawa = h * (1 - twist)
    vectors, fermions, cross_curvatures = [], [], []
    for a, stack in enumerate(nodes):
        for b, other in enumerate(nodes):
            w = cycle ** (a - b)
            first = h * (1 / w - twist * w)
            second = h * (w - twist / w)
            for left in stack:
                for right in other:
                    mass = abs(first * left + second * right)
                    if a == b:
                        vector = 2 * gauge**2 * abs(left - right)**2
                        vectors.append(vector)
                        midpoint = np.sqrt(vector + mass**2 / 4)
                        fermions.extend([(midpoint - mass / 2)**2, (midpoint + mass / 2)**2])
                    else:
                        fermions.append(mass**2)
                        split = abs(np.conj(yukawa) * (first * np.conj(left)**2
                                                       + second * np.conj(right)**2))
                        # A constrained Hessian on the equal-modulus sphere.
                        if abs(abs(left) - abs(right)) < 1e-10:
                            omega2 = 2 * abs(yukawa * left)**2
                            cross_curvatures.append(mass**2 - omega2 - split)
    vectors, fermions = np.array(vectors), np.array(fermions)
    return vectors, fermions, np.array(cross_curvatures)


def response(order, nodes, flux=1):
    vectors, fermions, curvatures = spectrum(order, nodes, flux=flux)
    residuals = [len(fermions) / 4 - len(vectors), sum(fermions) / 4 - sum(vectors)]
    assert max(abs(x) for x in residuals) < 2e-9
    coefficient = 2 * (sum(xlogy(fermions, fermions)) / 4 - sum(xlogy(vectors, vectors)))
    return float(coefficient), float(np.min(curvatures))


def polygon_nodes(rank, registry):
    vertices = np.exp(2j * np.pi * np.arange(rank) / rank)
    return [vertices * np.exp(2j * np.pi * node * registry / rank) for node in range(3)]


def adj(matrix):
    return matrix.conj().T


def norm2(matrix):
    return float(np.vdot(matrix, matrix).real)


def bracket(left, right):
    return left @ right - right @ left


def torus(order):
    phase = np.exp(2j * np.pi / order)
    first = np.diag(phase**np.arange(order))
    second = np.roll(np.eye(order), 1, axis=0)
    third = adj(first @ second)
    basis = np.ones(order, dtype=complex) / np.sqrt(order)
    columns = []
    for _ in range(order):
        columns.append(basis)
        basis = third @ basis
    cycle = np.column_stack(columns)
    links = (first, second, third)
    for index, link in enumerate(links):
        assert np.allclose(cycle @ link @ adj(cycle), links[(index + 1) % 3])
    assert np.allclose(cycle @ cycle @ cycle, (cycle @ cycle @ cycle)[0, 0] * np.eye(order))
    return links


def potential(order, charges, scalar, gauge=1.0, flux=1):
    """Trace of the three parent F terms and one D term after magnetic translations."""
    p = np.diag(np.exp(2j * np.pi * np.asarray(charges) / 3))
    fields = [scalar, p @ scalar @ adj(p), adj(p) @ scalar @ p]
    tau = np.exp(-2j * np.pi * flux / order)
    energy_f = sum(norm2(fields[i] @ fields[(i + 1) % 3]
                         - tau * fields[(i + 1) % 3] @ fields[i]) for i in range(3))
    energy_d = norm2(sum(bracket(z, adj(z)) for z in fields))
    return gauge**2 * (2 * energy_f / 9 + energy_d / 18)


def parent_check(order, rng):
    links = torus(order)
    gauge = .71
    parent_gauge = gauge * np.sqrt(order)
    charges = [0, 0, 1, 2]
    p = np.diag(np.exp(2j * np.pi * np.array(charges) / 3))
    z = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
    orbit = [z, p @ z @ adj(p), adj(p) @ z @ p]
    fields = [np.kron(link, field) / np.sqrt(3 * order) for link, field in zip(links, orbit)]
    parent = 2 * sum(norm2(bracket(fields[i], fields[(i+1) % 3])) for i in range(3))
    parent += norm2(sum(bracket(x, adj(x)) for x in fields)) / 2
    assert np.isclose(parent_gauge**2 * parent, potential(order, charges, z, gauge), rtol=1e-12)
    # A non-normal matrix probes the competition of D and F energies within one node.
    y2 = (8/3) * gauge**2 * np.sin(np.pi/order)**2
    gram = adj(z) @ z
    bound = y2 * np.trace(gram).real**2 / len(z)
    residual = y2 * norm2(gram - np.trace(gram) / len(z) * np.eye(len(z)))
    residual += (gauge**2 - y2) * norm2(bracket(z, adj(z))) / 2
    assert np.isclose(potential(order, [0]*4, z, gauge), bound + residual)


def numerical_hessian(function, point, step=0.001):
    axes = np.eye(len(point)) * step
    h = np.empty((len(point), len(point)))
    for i, first in enumerate(axes):
        for j in range(i + 1):
            second = axes[j]
            h[i, j] = h[j, i] = (function(point + first + second) + function(point - first - second)
                                - function(point + first - second) - function(point - first + second)) / (4*step**2)
    return h


def inspect_regular(order, rank, registry, check=False):
    nodes = polygon_nodes(rank, registry)
    value, curvature = response(order, nodes)
    if check:
        charges = np.repeat(np.arange(3), rank)
        diag = np.concatenate(nodes)
        base = np.diag(diag)
        omega2 = (16 / 3) * np.sin(np.pi/order)**2
        # Each pair of distinct cyclic characters gives four real, ungauged scalars.
        independent_min = np.inf
        for i, a in enumerate(charges):
            for j in range(i):
                if a == charges[j]:
                    continue
                def energy(x):
                    z = base.copy()
                    z[i,j] += (x[0] + 1j*x[1]) / np.sqrt(2)
                    z[j,i] += (x[2] + 1j*x[3]) / np.sqrt(2)
                    return potential(order, charges, z) - omega2 * norm2(z)
                hess = numerical_hessian(energy, np.zeros(4))
                independent_min = min(independent_min, eigvalsh(hess)[0])
        assert abs(independent_min - curvature) < 3e-5, (independent_min, curvature)
        verify_fermions(order, charges, diag)
    return {"N": order, "rank_per_node": rank, "registry": registry,
            "external_spin_response": value, "least_cross_shape_mass2": curvature}


def projected_masses(order, charges, bg, flux=1):
    """Direct projected cubic, gauge Yukawa and vector matrices in the local static background."""
    n = len(charges)
    p = np.diag(np.exp(2j*np.pi*charges/3))
    tau = np.exp(-2j*np.pi*flux/order)
    def rotate(z):
        return p @ z @ adj(p)
    def triple(a, b, c):
        b1, c1 = rotate(b), rotate(c)
        return np.sqrt(2/27)*np.trace(a @ (b1 @ rotate(c1) - tau * rotate(b1) @ c1))
    basis = [np.eye(n*n)[i].reshape((n,n)) for i in range(n*n)]
    gauge_basis = [m for i,m in enumerate(basis) if charges[i//n] == charges[i%n]]
    chiral = np.array([[3*(triple(bg,a,b) + triple(bg,b,a)) for b in basis] for a in basis])
    mixing = np.array([[np.sqrt(2)*np.trace(t @ bracket(adj(bg), z)) for z in basis]
                       for t in gauge_basis])
    masses = svdvals(np.block([[np.zeros((len(gauge_basis),)*2), mixing], [mixing.T, chiral]]))**2
    modes = []
    for i in range(n):
        for j in range(i+1):
            if charges[i] != charges[j]:
                continue
            unit = basis[i*n+j]
            if i==j:
                modes.append(unit)
            else:
                modes.extend([(unit+adj(unit))/np.sqrt(2),1j*(unit-adj(unit))/np.sqrt(2)])
    differences = np.stack([bracket(t,bg).ravel() for t in modes])
    vectors = np.maximum(eigvalsh(2*(differences @ adj(differences)).real),0.)
    return vectors, masses


def verify_fermions(order, charges, diagonal):
    vectors, masses = projected_masses(order,charges,np.diag(diagonal))
    nodes = [diagonal[charges == a] for a in range(3)]
    known_v, known_f, _ = spectrum(order, nodes)
    assert np.allclose(np.sort(masses), np.sort(known_f), atol=1e-10)
    assert np.allclose(vectors, np.sort(known_v), atol=1e-10)


@lru_cache(maxsize=32)
def mass_indices(order, charge_tuple, flux):
    n = len(charge_tuple)
    charges = np.array(charge_tuple)
    i, j = np.indices((n,n)).reshape(2,-1)
    a,b = i[charges[i]==charges[j]], j[charges[i]==charges[j]]
    phase = np.exp(2j*np.pi*(charges[i]-charges[j])/3)
    tau = np.exp(-2j*np.pi*flux/order)
    direct = np.sqrt(2/3)*(phase[:,None]*np.conj(phase[None,:])
                           -tau*np.conj(phase[:,None])*phase[None,:])*(j[:,None]==i[None,:])
    basis = []
    for h,k in zip(a,b):
        if h<k:
            continue
        unit = np.zeros((n,n),complex)
        unit[h,k] = 1
        if h==k:
            basis.append(unit)
        else:
            basis.extend([(unit+adj(unit))/np.sqrt(2),1j*(unit-adj(unit))/np.sqrt(2)])
    return i,j,a,b,direct,np.array(basis)


def fast_masses(order,charges,bg,flux):
    i,j,a,b,direct,basis = mass_indices(order,tuple(charges),flux)
    entry = direct * bg[j[None,:], i[:,None]]
    mixing = np.sqrt(2)*((j[None,:]==a[:,None])*adj(bg)[b[:,None],i[None,:]]
                         -(b[:,None]==i[None,:])*adj(bg)[j[None,:],a[:,None]])
    fermions = svdvals(np.block([[np.zeros((len(a),)*2),mixing],[mixing.T,entry+entry.T]]))**2
    difference = (basis @ bg - bg @ basis).reshape(len(basis),-1)
    vectors = np.maximum(eigvalsh(2*(difference @ adj(difference)).real),0.)
    return vectors,fermions


def total_energy(order,charges,bg,flux):
    vectors,fermions = fast_masses(order,charges,bg,flux)
    assert abs(sum(fermions)/4-sum(vectors))<1e-8
    coeff = 2*(sum(xlogy(fermions,fermions))/4 - sum(xlogy(vectors,vectors)))
    return potential(order,charges,bg,flux=flux)/coeff**2, coeff


def nonnormal_background(order, flux, full_shape):
    # The square of each internal block is zero. Its Frobenius norm equals that of diag(1,-1).
    bg = block_diag(*([np.array([[0.,np.sqrt(2)],[0.,0.]])]*3)).astype(complex)
    charges = np.repeat(np.arange(3),2)
    vectors, fermions = projected_masses(order,charges,bg,flux)
    fast_v,fast_f = fast_masses(order,charges,bg,flux)
    assert np.allclose(np.sort(fermions),np.sort(fast_f)) and np.allclose(vectors,fast_v)
    assert abs(sum(fermions)/4-sum(vectors))<1e-9
    coeff = 2*(np.sum(xlogy(fermions,fermions))/4-np.sum(xlogy(vectors,vectors)))
    out = {"N":order,"flux":flux,"response":float(coeff)}
    if full_shape:
        def potential_on_ray(x):
            z = (x[:36]+1j*x[36:]).reshape(6,6)
            return potential(order,charges,z,flux=flux)/norm2(z)**2
        point = np.r_[bg.real.ravel(),bg.imag.ravel()]
        hess = numerical_hessian(potential_on_ray,point,step=.00018)
        tangent = null_space(point[None,:])
        fields = eigvalsh(tangent.T @ hess @ tangent)
        out.update(minimum=float(fields[0]),negative=int(sum(fields < -2e-6)))
        # A lower nearby V/A^2 is decisive even when massless fields make its Hessian singular.
        direction = np.zeros_like(bg)
        direction[0,3] = 1.
        u0,_ = total_energy(order,charges,bg,flux)
        changes=[]
        for eps in [.02,.01,.005,.0025]:
            up,ap=total_energy(order,charges,bg+eps*direction,flux)
            um,am=total_energy(order,charges,bg-eps*direction,flux)
            assert min(ap,am)>0
            changes.append((up+um-2*u0)/(u0*eps**2))
        out["E03_relative_second_differences"] = changes
    return out


def cycle_test(order,flux):
    charges = np.arange(3)
    base = np.roll(np.eye(3),1,axis=0)
    energy,coeff = total_energy(order,charges,base,flux)
    row,col = np.where(~np.eye(3,dtype=bool))
    start = np.r_[base[row,col],np.zeros(6)]
    def restricted(x):
        z = np.zeros((3,3),complex)
        z[row,col] = x[:6] + 1j*x[6:]
        return total_energy(order,charges,z,flux)[0]
    physical_curvatures=[]
    for step in [.001,.0005]:
        # The common scale and three link phases span the four flat directions.
        hess=numerical_hessian(restricted,start,step)
        fixed=np.zeros((4,12))
        fixed[0,:]=start
        for index,j in enumerate(np.flatnonzero(start)):
            fixed[index+1,j+6]=1.
        tangent=null_space(fixed)
        physical_curvatures.append(float(eigvalsh(tangent.T@hess@tangent)[0]))
    def unproject(x):
        return (x[:9]+1j*x[9:]).reshape(3,3)
    point=np.r_[base.ravel(),np.zeros(9)]
    gauge=[1j*bracket(np.diag(t),base) for t in np.eye(3)[:2]]
    physical=null_space(np.array([np.r_[g.real.ravel(),g.imag.ravel()] for g in gauge]))
    hess=numerical_hessian(lambda x:potential(order,charges,unproject(x),flux=flux),point,.0003)/2
    masses,modes=np.linalg.eigh(physical.T@hess@physical)
    negative=masses < -1e-5
    y2 = 8*np.sin(np.pi*flux/order)**2/3
    mass_c2 = 6-2*y2
    assert np.isclose(masses[0],mass_c2 - np.sqrt(mass_c2*y2),atol=2e-6)
    high = np.sqrt(6+y2/4)
    predicted=[0.,4*y2]+[y2]*2+[mass_c2]*4
    for sign in [-1,1]:
        predicted.extend([(high+sign*np.sqrt(y2)/2)**2]*2)
    direct_v,direct_f = projected_masses(order,charges,base,flux)
    assert np.allclose(direct_v,[0,6,6]) and np.allclose(np.sort(direct_f),np.sort(predicted))
    diagonal_weights=[norm2(np.diag(unproject(physical@mode))) for mode in modes[:,negative].T]
    assert all(abs(d-.5)<2e-5 for d in diagonal_weights)
    return {"N": order,"flux":flux,"response":coeff,"V_over_A2":energy,
            "least_eight_shape_curvatures_two_steps":physical_curvatures,
            "least_bare_physical_mass2":float(masses[0]),"negative_bare_modes":int(sum(negative)),
            "mean_diagonal_fraction_of_negative_modes":float(np.mean(diagonal_weights))}


def radial_frequencies(k2, d, mixing):
    # Solve the two linear wave equations as a first-order initial-value problem.
    gyroscope = np.array([[0., mixing], [-mixing, 0.]])
    generator = np.block([[np.zeros((2,2)), np.eye(2)], [-np.diag([k2 + d, k2]), gyroscope]])
    frequencies = -np.linalg.eigvals(generator)**2
    assert np.max(abs(frequencies.imag)) < 2e-7
    return np.sort(frequencies.real)[::2]


def dynamics():
    rows = []
    for k in [0., .5, np.sqrt(7)/4, 1., 2.]:
        common = radial_frequencies(k*k, 2, 2)
        shape = radial_frequencies(k*k, -1, 2)
        for d, roots in [(2, common),(-1, shape)]:
            assert np.allclose(np.poly(roots), [1,-(2*k*k + d + 4), k*k*(k*k + d)])
        rows.append([float(k), float(common[0]), float(shape[0])])
    # The charged longitudinal vector is retained. The temporal component obeys Gauss' law.
    for order in [5,11,31]:
        omega = np.sqrt(2/3)*np.sin(np.pi/order)  # unit charged vector mass
        for k in [0., .33,.75,1.7]:
            K = 1 + k*k
            scalar = k*k+1-2*omega**2+4*omega**2/K
            rotation = 2*omega*k/np.sqrt(K)
            gyro = np.array([[0., rotation], [-rotation, 0.]])
            matrix = np.block([[np.zeros((2,2)),np.eye(2)],[-np.diag([scalar,K]),gyro]])
            exact = K+omega**2 + np.array([-1,1])*np.sqrt(omega**4+4*omega**2*k*k)
            assert np.allclose(np.sort((-np.linalg.eigvals(matrix)**2).real)[::2], exact)
    return rows


def coulomb_branch(order, points):
    phase = np.exp(2j*np.pi/order)
    masses = 2 * abs(points[:,None] - points[None,:])**2
    twisted = 2 * abs(points[:,None] - phase*points[None,:])**2
    assert abs(sum(points)) < 1e-12 and abs(np.sum(masses-twisted)) < 1e-10
    coeff = np.sum(xlogy(twisted,twisted) - xlogy(masses,masses))
    # Finite small-time subtractions avoid cancellation of the zeroth/first moments.
    def heat(t):
        if t < 1e-4:
            return sum(((-1)**k * t**(k-2) * np.sum(twisted**k-masses**k)
                        / float(np.prod(np.arange(1,k+1)))) for k in range(2,8))
        return np.sum(np.exp(-t*twisted)-np.exp(-t*masses))/t**2
    integral = quad(heat,0,1,epsabs=2e-9)[0]+quad(heat,1,np.inf,epsabs=2e-9)[0]
    assert np.isclose(coeff,integral,atol=2e-8)
    return float(coeff)


def comparisons():
    # eV, metres and a reference Hubble parameter. These inputs are observational comparisons.
    m_e, alpha_em, reduced_planck, hbar_c = 510998.95, 1/137.036, 2.435e27, 1.973269804e-7
    unit_charge = np.sqrt(4*np.pi*alpha_em)
    hubble = 67.4*1000/3.08567758149e22*6.582119569e-16
    density_limit = 3*reduced_planck**2*hubble**2
    # Equation (44) of Heckel et al.; conservative two-sided normal envelope.
    spin_bound = (0.50+1.96*1.13)*1e-19
    min_N_spin = np.pi/np.arcsin(2*spin_bound/(m_e*np.sqrt(2/3)))
    min_N_density = np.pi/np.arcsin(unit_charge*np.sqrt(2*density_limit)/m_e**2)
    ze_ti = .90*22/47.867+.06*13/26.982+.04*23/50.942
    ze_pt = .90*78/195.084+.10*45/102.906
    electron_per_unit = .00054858
    earth = .49*electron_per_unit
    difference = (ze_ti-ze_pt)*electron_per_unit
    eta_limit = (1.5+1.96*np.hypot(2.3,1.5))*1e-15
    beta_limit = eta_limit/(earth*difference)
    return {"reference_H_eV":hubble, "critical_density_eV4":density_limit,
            "helicity_95_normal_envelope_eV":spin_bound,"electron_rank_from_spin":min_N_spin,
            "electron_rank_from_positive_density":min_N_density,
            "minimum_range_if_abs_s_at_most_one_m":hbar_c/(2*np.sqrt(2)*spin_bound),
            "electron_mass_force_95_envelope":beta_limit, "alloy_electron_fraction_difference":difference,
            "maximum_abs_df_dh_electron":m_e/unit_charge/reduced_planck*np.sqrt(beta_limit/2),
            "gravity_strength_range_if_density_at_most_critical_m":hbar_c/(2*hubble),
            "minimum_curvature_coupling_at_electron_scale":(m_e/hubble)**2/2880}


def varying_planck_mass():
    rows=[]
    # M_P=1, R near 1.1. The Einstein-frame radial kinetic metric is evaluated at the extremum.
    for baseline,xi in [(1.,0.),(1.,.4),(.1,1.),(0.,1.)]:
        r0,quartic=1.1,.73
        def radius(r):
            return r/np.sqrt(baseline+xi*r*r)
        f=radius(r0)
        omega=np.sqrt(quartic)*f
        charge=f*f*omega
        F=baseline+xi*r0*r0
        kinetic=1/F+1.5*(2*xi*r0/F)**2
        slope=baseline/(F**1.5*np.sqrt(kinetic))
        def static(r):
            return quartic*radius(r)**4/4-omega**2*radius(r)**2/2
        def fixed_charge(r):
            return quartic*radius(r)**4/4+charge**2/(2*radius(r)**2)
        static_mass=2*slope**2*omega**2
        for fn,expected in [(static,static_mass),(fixed_charge,3*static_mass)]:
            step=.00025
            measured=(fn(r0+step)+fn(r0-step)-2*fn(r0))/(step**2*kinetic)
            assert np.isclose(measured,expected,rtol=3e-5,atol=6e-8)
        beta=2*slope*slope/f**2
        density=3*quartic*f**4/4
        assert np.isclose(static_mass,4*beta*density/3)
        rows.append({"bare_F":baseline,"xi":xi,"static_mass2":static_mass,"beta":beta})
    return rows


def main():
    rng = np.random.default_rng(314159)
    for order in [3,5,7,9]:
        parent_check(order,rng)
    regular = [inspect_regular(order,rank,registry,check=(rank==2 and order in [5,11]))
               for order in [5,7,11,17,31,67] for rank in [2,3,4,5,8] for registry in [0,1/3]]
    for order in [5,11,31]:
        nodes = [rng.normal(size=3)+1j*rng.normal(size=3) for _ in range(3)]
        v,f,_ = spectrum(order,nodes)
        traces = np.array([sum(node) for node in nodes])
        common = np.mean(traces)
        predicted = 3*sum(abs(traces-common)**2) + 12*np.sin(np.pi/order)**2*abs(common)**2
        assert np.isclose(sum(f)/4 - sum(v),predicted)
        if order == 5:
            verify_fermions(order,np.repeat(np.arange(3),3),np.concatenate(nodes))
    cloud = rng.normal(size=5)+1j*rng.normal(size=5)
    cloud -= np.mean(cloud)
    coulomb = {str(order):coulomb_branch(order,cloud) for order in [3,5,11,31]}
    regular_cloud = np.exp(2j*np.pi*np.arange(5)/5)
    assert abs(coulomb_branch(5,regular_cloud)) < 1e-10
    cycles=[cycle_test(n,(n-1)//2) for n in [5,7,11,23]]
    winding = []
    for order in [5,7,11,17]:
        for flux in range(1,order//2+1):
            if gcd(order,flux)==1:
                check_shape = order in [5,11] and flux in [1,order//2]
                winding.append(nonnormal_background(order,flux,check_shape))
    cycle = np.roll(np.eye(3),1,axis=0)
    sign_change=brentq(lambda fraction:total_energy(1,np.arange(3),cycle,fraction)[1],.36,.38)
    # One off-node, non-diagonal background verifies the fast tensor contraction.
    charges=np.repeat(np.arange(3),2)
    trial=rng.normal(size=(6,6))+1j*rng.normal(size=(6,6))
    direct=projected_masses(5,charges,trial,2)
    fast=fast_masses(5,charges,trial,2)
    assert all(np.allclose(np.sort(first),np.sort(second)) for first,second in zip(direct,fast))
    result = {"unit_gauge_coupling_and_eigenvalue_radius":regular,
              "single_link_centred_cloud":coulomb, "wave_branches_in_rotation_units":dynamics(),
              "nilpotent_blocks":winding,"three_node_cycles":cycles,"cycle_spin_zero_between_036_and_038":sign_change,
              "nonminimal_radial_checks":varying_planck_mass(),"observational_comparisons":comparisons()}
    target = Path(__file__).resolve().parents[1]/"verification"/"cat-magnetic-orbifold-results.json"
    target.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print(f"Verified {len(regular)} regular spectra and the projected matrix, wave and heat-kernel checks.")


if __name__ == "__main__":
    main()
