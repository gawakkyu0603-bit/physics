"""One-loop pressure, spatial curvature and time-dependent shear of the projected chiral sector."""
import json
import math
from decimal import Decimal, localcontext
from pathlib import Path

import numpy as np
from scipy.integrate import quad, quad_vec, solve_bvp
from scipy.optimize import brentq


# Use r as the unit of energy. Decimal preserves the UV subtraction between
# rotating and nonrotating kernels even after mapping the infinite interval.
D = Decimal
PI2 = math.pi**2


def modes(p, x):
    """x=mu^2/r^2. Real scalar pole residues are (uu,vv,Im uv)."""
    p2 = p*p
    mu = x.sqrt()
    a, b = p2+6-x, p2+2-x
    split = 2*(1+x*(p2+4)).sqrt()
    high2 = p2+4+x+split
    low2 = a*b/high2
    pole_data = []
    for square, difference in ((low2, 2*split), (high2, -2*split)):
        energy = square.sqrt()
        pole_data.append((energy, (b-square)/(2*energy*difference),
                          (a-square)/(2*energy*difference), mu/difference))
    helicities = (p-mu/2, -p-mu/2)
    fermions = [(h, (h*h+4).sqrt()) for h in helicities]
    return pole_data, fermions


def kernels(p, x):
    scalars, fermions = modes(p, x)
    bs = sum(entry[0] for entry in scalars)
    fs = sum(entry[1] for entry in fermions)
    dr = sum(entry[1]+entry[2] for entry in scalars)
    boson_shear = D(0)
    for e, u, v, w in scalars:
        for f, a, b, c in scalars:
            boson_shear += (u*a+v*b-2*w*c)/(e+f)**3
    boson_shear *= 8*p**4/15
    fermion_shear = D(0)
    for i, (h, e) in enumerate(fermions):
        for j, (l, f) in enumerate(fermions):
            angular = D(4)/15 if i == j else D(2)/5
            overlap = (1+(4-h*l)/(e*f))/2
            fermion_shear += angular*p*p*overlap/(2*(e+f)**3)
    return bs, fs, dr, boson_shear, fermion_shear


def subtracted(p_float, x_float):
    with localcontext() as ctx:
        ctx.prec = 56
        p, x = D(str(p_float)), D(str(x_float))
        active = kernels(p, x)
        reference = kernels(p, D(0))
        db, df, dp, dtb, dtf = [a-b for a, b in zip(active, reference)]
        # The last column is the lapse-independent flat determinant. A smooth
        # subtraction fixes its finite convention at unit reference scale.
        b, f = active[:2]
        flat = p*p*(b-f)+(1+x)*p**2/(p*p+1)**(D(3)/2)
        return np.array([float(v) for v in (db, df, p*p*dp, p*p*dtb, p*p*dtf, flat)])


def integrals(x):
    value, error = quad_vec(lambda p: subtracted(p, x), 0, np.inf,
                            epsabs=2e-10, epsrel=2e-10)
    db, df, radial, tb, tf, flat = value
    np.testing.assert_allclose(df, x/4, atol=1e-10)
    np.testing.assert_allclose(radial, -db/2, atol=1e-10)
    # Independent composite Gauss integration on a compactified interval.
    nodes, weights = np.polynomial.legendre.leggauss(72)
    test = np.zeros(6)
    for lo, hi in ((0., .12), (.12, .55), (.55, 1.)):
        s = lo+(hi-lo)*(nodes+1)/2
        for t, w in zip(s, weights):
            test += w*(hi-lo)/2*subtracted(t/(1-t), x)/(1-t)**2
    np.testing.assert_allclose(test, value, rtol=2e-8, atol=2e-10)
    responses = []
    for xi in (0., 1/6):
        space = ((6*xi-1)*db/12-x/96)/(2*PI2)
        time = (tb+tf+xi*db/2)/(2*PI2)
        responses.append(dict(xi=xi, spatial_shift_over_r2=space, temporal_shift_over_r2=time))
    difference = (tb+tf+db/12+x/96)/(2*PI2)
    assert all(abs(row["temporal_shift_over_r2"]-row["spatial_shift_over_r2"]-difference)<1e-12
               for row in responses)
    return dict(mu_squared_over_r_squared=x, integrated_boson_sum=db,
                integrated_fermion_sum=df, time_shear_boson_integral=tb,
                time_shear_fermion_integral=tf, subtracted_flat_integral=flat,
                tensor_time_minus_space_over_r2=difference, reference_shifts=responses)


def independent_shear(p, x):
    """Euclidean boson bubble and direction-resolved fermion Hamiltonian."""
    mu = math.sqrt(x)
    def scalar_integrand(v):
        inverse = np.array([[v*v+p*p+6-x, -2*mu*v], [2*mu*v, v*v+p*p+2-x]])
        propagator = np.linalg.inv(inverse)
        derivative = -propagator @ np.array([[2*v, -2*mu], [2*mu, 2*v]]) @ propagator
        return np.trace(derivative @ derivative)
    boson = 2*p**4/15 * quad(scalar_integrand, 0, np.inf, epsabs=1e-11)[0]/math.pi
    pauli = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
    directions = [(sign*axis, 1/15) for axis in np.eye(3) for sign in (-1, 1)]
    directions += [(np.array([i,j,k])/math.sqrt(3), 3/40)
                   for i in (-1,1) for j in (-1,1) for k in (-1,1)]
    fermion = 0.
    for direction, weight in directions:
        momentum = p*direction
        h = np.kron(pauli[2], np.tensordot(momentum, pauli, 1)-mu*np.eye(2)/2)
        h += 2*np.kron(pauli[0], np.eye(2))
        derivative = np.kron(pauli[2], -momentum[0]*pauli[0]+momentum[1]*pauli[1])
        energies, vectors = np.linalg.eigh(h)
        matrix = vectors[:,2:].conj().T @ derivative @ vectors[:,:2]
        gaps = energies[2:,None]-energies[None,:2]
        fermion += weight*np.sum(abs(matrix)**2/gaps**3)/2
    expected = [float(v) for v in kernels(D(str(p)), D(str(x)))[3:]]
    np.testing.assert_allclose([boson, fermion], expected, rtol=2e-8, atol=2e-11)


def sphere_check(x, xi):
    """Measure the K coefficient with discrete spatial modes and a common UV cutoff."""
    cutoff = 12.
    def b(p2, z):
        return np.sqrt(2*(p2+4+z+np.sqrt((p2+6-z)*(p2+2-z))))
    def f(p, z):
        shift = math.sqrt(z)/2
        return np.hypot(p+shift, 2)+np.hypot(p-shift, 2)
    def smooth(p):
        return np.exp(-(p/cutoff)**2)
    def rotation(p2):
        return b(p2, x)-b(p2, 0)
    def fermion(p):
        return f(p,x)-f(p,0)
    def db(p, z):
        return (1+(p*p+4-z)/np.sqrt((p*p+6-z)*(p*p+2-z)))/b(p*p,z)
    flat = quad(lambda p: p*p*(rotation(p*p)-fermion(p))*smooth(p), 0, 8*cutoff,
                epsabs=2e-10)[0]
    predicted = quad(lambda p: ((6*xi-1)*p*p*(db(p,x)-db(p,0))+fermion(p)/4)*smooth(p),
                     0, 8*cutoff, epsabs=2e-10)[0]
    slopes = []
    for radius in (6., 12., 24.):
        curvature = radius**-2
        boson_p = np.arange(1, int(8*cutoff*radius)+1)/radius
        fermion_p = boson_p+0.5/radius
        bosons = boson_p**2*rotation(boson_p**2+(6*xi-1)*curvature)*smooth(boson_p)
        fermions = (fermion_p**2-curvature/4)*fermion(fermion_p)*smooth(fermion_p)
        slopes.append(((bosons.sum()-fermions.sum())/radius-flat)/curvature)
    extrapolated = (4*slopes[-1]-slopes[-2])/3
    np.testing.assert_allclose(extrapolated, predicted, atol=1e-7)
    return dict(x=x, xi=xi, continuum_slope=predicted, sphere_slopes=slopes)


def clock_domains():
    """Neumann charge constraint and acoustic transfer through two chambers and a tube."""
    from scipy.linalg import solve
    n = 61
    step = 1/n
    incidence = np.diff(np.eye(n), axis=0)/step
    laplacian = incidence.T @ incidence
    source = 0.3+np.sin(2*np.pi*(np.arange(n)+.5)*step)+0.4*np.cos(5*np.pi*(np.arange(n)+.5)*step)
    mass2 = 17.
    matrix = np.block([[laplacian+mass2*np.eye(n), -mass2*np.ones((n,1))],
                       [2*np.ones((1,n))/n, np.ones((1,1))]])
    solution = solve(matrix, np.r_[-mass2*source, source.mean()])
    np.testing.assert_allclose(solution[-1], source.mean(), atol=1e-12)
    eigen, basis = np.linalg.eigh(laplacian)
    filter_response = eigen/(eigen+mass2)
    filter_response[0] = 1
    np.testing.assert_allclose(source+solution[:-1], basis @ (filter_response*(basis.T@source)),
                               atol=2e-12)
    def duct(k, length, area):
        phase = k*length
        return np.array([[np.cos(phase), np.sin(phase)/(area*k)],
                         [-area*k*np.sin(phase), np.cos(phase)]])
    cases = []
    for area in (.02, .005, .001):
        predicted = math.sqrt(area/.5*(1/1.2+1/(.8*1.4)))
        def residual(k):
            propagator = duct(k,1.4,.8) @ duct(k,.5,area) @ duct(k,1.2,1)
            return propagator[1,0]
        actual = brentq(residual, predicted/2, predicted*1.5)
        cases.append(dict(tube_area=area, exact_wave_number=actual, reservoir_limit=predicted,
                          relative_error=abs(actual/predicted-1)))
    assert cases[2]["relative_error"]<cases[1]["relative_error"]<cases[0]["relative_error"]<.03
    return cases


def quantum_radius(flat_value):
    """Fixed-charge tadpole and the leading physical width of the radial resonance."""
    def slope(p_float):
        with localcontext() as ctx:
            ctx.prec = 56
            p = D(str(p_float))
            p2, mu = p*p, D(2).sqrt()
            h = ((p2+4)*p2).sqrt()
            boson = (2*(p2+6+h)).sqrt()
            db = (1-(p2+2)/h)/boson
            left, right = p-mu/2, p+mu/2
            df = (right/(right**2+4).sqrt()-left/(left**2+4).sqrt())/(4*mu)
            return float(p2*(db-df)+p2/(p2+1)**(D(3)/2))
    derivative = quad(slope, 0, np.inf, epsabs=1e-11)[0]
    step = 1e-5
    neighbor = quad(lambda p: subtracted(p, 2-step)[5], 0, np.inf, epsabs=2e-11)[0]
    np.testing.assert_allclose((flat_value-neighbor)/step, derivative, atol=3e-5)
    frequency_shift = flat_value/3+.25
    radius_shift = (derivative-frequency_shift)/2
    # Obtain normalized canonical eigenvectors from the inverse propagator.
    heavy = math.sqrt(12)
    p2_star = 1+2*math.sqrt(7)
    def leg(p, energy):
        mu = math.sqrt(2)
        inv = np.array([[p*p+4-energy**2, -2j*mu*energy],
                        [2j*mu*energy, p*p-energy**2]])
        energies, vectors = np.linalg.eigh(inv)
        vector = vectors[:,np.argmin(abs(energies))]
        norm = np.array([[2*energy, 2j*mu], [-2j*mu, 2*energy]])
        return vector/math.sqrt((vector.conj() @ norm @ vector).real)
    initial = leg(0, heavy)
    def low_energy(p):
        return p*math.sqrt((p*p+4)/(p*p+6+math.sqrt(36+8*p*p)))
    def amplitude2(p):
        u, v = leg(p, low_energy(p)).conj()
        amplitude = 4*(initial[0]*(3*u*u+v*v)+2*initial[1]*u*v)
        return abs(amplitude)**2
    pole = brentq(lambda p: 2*low_energy(p)-heavy, 2, 3)
    np.testing.assert_allclose(pole**2, p2_star, atol=1e-13)
    analytic = math.sqrt(p2_star)*(p2_star-9)**2/(48*math.pi*math.sqrt(3)*(p2_star+3)*(p2_star-1))
    group_speed = (low_energy(pole+1e-5)-low_energy(pole-1e-5))/2e-5
    rate = pole**2*amplitude2(pole)/(8*math.pi*group_speed*heavy)
    np.testing.assert_allclose(rate, analytic, rtol=1e-9)
    def broadened(width):
        def integrand(p):
            delta = math.exp(-.5*((2*low_energy(p)-heavy)/width)**2)/(math.sqrt(2*math.pi)*width)
            return p*p*amplitude2(p)*delta/(4*math.pi*heavy)
        return quad(integrand, pole-.12, pole+.12, points=[pole], epsabs=1e-12)[0]
    broaden = [broadened(width) for width in (.012,.006)]
    np.testing.assert_allclose((4*broaden[1]-broaden[0])/3, analytic, rtol=2e-8)
    return dict(flat_shape_derivative=derivative, fractional_radius_per_y2_over_4pi2=radius_shift,
                fractional_mu_per_y2_over_4pi2=frequency_shift, decay_momentum_over_r=pole,
                breathing_width_over_energy_y2=analytic, broadened_rates=broaden)


def curved_neck():
    """Solve the nonlinear radial equation before integrating the phase compliance."""
    mu, xi, a = 1., 1/6, .05
    r2 = mu**2/2
    area = 4*math.pi*a*a
    kappa = math.sqrt(2*xi/a**2-mu**2)
    quartic = r2/kappa**2
    out = []
    for length in (8., 12., 16.):
        grid = np.linspace(0, length/2, 161)
        seed = np.array([np.cosh(grid-length/2), np.sinh(grid-length/2)])/np.cosh(length/2)
        def equation(t, y):
            return np.vstack((y[1], y[0]+2*quartic*y[0]**3))
        profile = solve_bvp(equation, lambda left, right: [left[0]-1, right[1]],
                            grid, seed, tol=2e-10, max_nodes=6000)
        assert profile.success, profile.message
        compliance = 2*quad(lambda t: 1/profile.sol(t)[0]**2, 0, length/2, epsrel=1e-10)[0]
        coefficient = 1/compliance
        high = 1/math.sinh(length)
        factor = math.sqrt(1+2*quartic)
        low = factor/math.sinh(factor*length)
        assert low <= coefficient <= high
        h, dh = profile.sol(grid)
        u, u_c = r2*h**2, r2*h[-1]**2
        gradient = r2*kappa**2*dh**2
        null_stress = mu**2*u+(1-2*xi)*gradient-2*xi*(kappa**2*u+2*u*u)
        polynomial = ((1-6*xi)*u**2+(mu**2+(1-4*xi)*kappa**2)*u
                      -(1-2*xi)*(kappa**2*u_c+u_c**2))
        np.testing.assert_allclose(null_stress, polynomial, rtol=3e-9, atol=2e-9)
        assert null_stress[0] > 0 > null_stress[-1]
        # Equal chambers of proper volume 1000 mu^-3, at external frequency .003 mu.
        omega_j2 = 2*area*kappa*coefficient/(3*1000)
        omega_upper2 = 2*area*kappa*high/(3*1000)
        error = omega_j2/(.003**2-omega_j2)
        upper_error = omega_upper2/(.003**2-omega_upper2)
        inertia = 2/.01**2  # Example for a weakly coupled semiclassical phase.
        charging_energy = 2/(3*inertia*r2*1000)
        out.append(dict(kappa_length=length, stiffness_divided_by_J_area_r2_kappa=coefficient,
                        comparison_bounds=[low, high], omega_j_squared_over_mu2=omega_j2,
                        clock_relative_error=error, clock_upper_error=upper_error,
                        endpoint_and_midpoint_null_stress_over_J=[null_stress[0], null_stress[-1]],
                        josephson_over_charging_at_y_001=omega_j2/charging_energy**2))
    assert out[-1]["clock_upper_error"] < 1e-5 < out[-2]["clock_relative_error"]
    return out


if __name__ == "__main__":
    table = [integrals(x) for x in (0., .125, .5, 1., 1.8, 2.)]
    for x in (0., .7, 2.):
        for p in (.2, 1.1, 3.):
            independent_shear(p, x)
    defect = table[-1]["tensor_time_minus_space_over_r2"]
    hubble_ev = 67.4*1000/3.085677581491367e22*6.582119569e-16
    reduced_planck_ev = 2.435e27
    result = dict(renormalized_rotation=table, discrete_sphere=[sphere_check(1.1, xi) for xi in (0., 1/6)],
                  acoustic_chambers=clock_domains(), curved_neck=curved_neck(),
                  quantum_radius=quantum_radius(table[-1]["subtracted_flat_integral"]),
                  one_day_clock_period_ratio=math.sqrt(1+1e5),
                  minimum_tensor_coefficient_over_r2=defect/(6e-15-(3e-15)**2),
                  uniform_density_ceiling=dict(radius_eV_per_sqrt_y=math.sqrt(hubble_ev*reduced_planck_ev),
                      leading_speed_deficit_per_y=defect*hubble_ev/(2*reduced_planck_ev)))
    target = Path(__file__).resolve().parents[1]/"verification"/"cat-rotating-response-results.json"
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
