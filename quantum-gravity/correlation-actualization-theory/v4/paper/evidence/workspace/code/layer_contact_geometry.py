"""Radial gravitational constraints and normalization along the proposed layer circle."""
import math

import numpy as np
from scipy.integrate import quad, solve_ivp


def taper(radius, inner, outer):
    """Unit plateau with four continuous derivatives at each endpoint."""
    if radius <= inner:
        return 1., 0., 0.
    if radius >= outer:
        return 0., 0., 0.
    width = outer-inner
    x = (radius-inner)/width
    # Evaluate near the zero end by symmetry to preserve the small residual.
    y = min(x, 1-x)
    cumulative = y**5*(126+y*(-420+y*(540+y*(-315+70*y))))
    value = 1-cumulative if x <= .5 else cumulative
    slope = -630*x**4*(1-x)**4/width
    curvature = -2520*x**3*(1-x)**3*(1-2*x)/width**2
    return value, slope, curvature


def compact_collapse_data(case):
    core, material_edge, reference_core, exterior = (2.2, 5.5, 5.75, 9.)
    p, s = case.fraction, case.amplitude
    shell_inner, shell_outer = 6., 7.
    boundaries = [core, material_edge, reference_core, shell_inner, shell_outer, exterior]
    shell_loads = np.zeros(2)
    def shell_shape(r):
        if not shell_inner < r < shell_outer:
            return 0.
        return ((r-shell_inner)*(shell_outer-r))**5
    shell_norm = quad(lambda r: r*r*shell_shape(r), shell_inner, shell_outer)[0]
    def background(radius, active):
        w, dw, ddw = taper(radius, core, material_edge)
        z, dz, _ = taper(radius, reference_core, exterior)
        field = s*w if active else 0.
        slope = s*dw if active else 0.
        second = s*ddw if active else 0.
        f = 1+case.xi*field**2
        df = 2*case.xi*field*slope
        ddf = 2*case.xi*(slope**2+field*second)
        density = case.radiation0*w**4+(case.clock0*z)**2/2+shell_loads[int(active)]*shell_shape(radius)/shell_norm
        density += case.rod**2*((z+radius*dz)**2+2*z*z)/2
        density += (slope**2+case.mass2*field**2)/2+case.quartic*field**4/4
        density += case.contact*p*(1-p)*(s*w)**4/2
        b = 1+radius*df/(2*f)
        effective = density+ddf+(2*df/radius if radius else 0.)
        return f, b, effective, df

    def integrated(radius, active):
        if radius == 0:
            f, _, effective, _ = background(0, active)
            return effective/(3*f)
        def integrand(r):
            f, b, effective, _ = background(r, active)
            return r*r*b*effective/math.sqrt(f)
        value = quad(integrand, 0., radius, points=[t for t in boundaries if t < radius],
                     epsabs=1e-12, epsrel=3e-13)[0]
        return value/(radius**3*math.sqrt(background(radius, active)[0]))

    original_masses = [exterior**3*integrated(exterior, active) for active in (False, True)]
    # Positive extra radiation in a shell fixes the exterior mass of every sector.
    shell_loads[:] = max(original_masses)-np.array(original_masses)
    outputs = []
    for active in [False, True]:
        def equation(r, y):
            f, b, effective, _ = background(r, active)
            return (b*effective/f-(2+b)*y)/r
        solved = solve_ivp(equation, (core, exterior+2), [integrated(core, active)],
                           method="DOP853", rtol=3e-12, atol=4e-14, max_step=.12, dense_output=True)
        assert solved.success
        radii = np.linspace(core+.03, exterior+.7, 23)
        quadrature_error = constraint_error = 0.
        for r in radii:
            y = integrated(r, active)
            assert y > 0
            quadrature_error = max(quadrature_error, abs(solved.sol(r)[0]-y))
            f, b, effective, df = background(r, active)
            angular = -math.sqrt(y)
            radial = (effective/f-y)/(2*angular)
            step = 3e-5
            slope = (-math.sqrt(integrated(r+step, active))+math.sqrt(integrated(r-step, active)))/(2*step)
            momentum = 2*f*((radial-angular)/r-slope)+radial*df
            constraint_error = max(constraint_error, abs(momentum))
        assert quadrature_error < 7e-11 and constraint_error < 3e-8
        angular = -math.sqrt(integrated(2., active))
        expansions = [2*(angular+1/2), 2*(angular-1/2)]
        assert max(expansions) < 0
        mass_radius = exterior**3*integrated(exterior, active)
        assert abs(mass_radius-(exterior+2)**3*integrated(exterior+2, active)) < 4e-12
        plot_radii = np.r_[np.linspace(0, 10, 65), np.linspace(11, 40, 30)]
        compactness = [float(r*r*integrated(float(r), active)) for r in plot_radii]
        outputs.append(dict(active=active, initial_h_core=angular, null_expansions_at_radius_2=expansions,
                            radii=plot_radii.tolist(), compactness=compactness,
                            schwarzschild_radius_parameter=mass_radius,
                            radial_quadrature_ode_discrepancy=quadrature_error,
                            radial_momentum_residual=constraint_error))
    assert abs(outputs[0]['schwarzschild_radius_parameter']-outputs[1]['schwarzschild_radius_parameter']) < 3e-12
    return dict(core_radius=core, material_edge=material_edge, reference_core=reference_core,
                uncompensated_mass_radii=original_masses, positive_shell_mass_radii=shell_loads.tolist(),
                vacuum_exterior_radius=exterior, sectors=outputs)


def causal_source_checks():
    # Static limit of the ten-spatial-dimensional retarded scalar Green function.
    point_prefactor = 3/(2*math.pi**5)
    infinite_line = 5*math.pi/16
    assert abs(point_prefactor*infinite_line-15/(32*math.pi**4)) < 3e-17
    def response(radius, half_length):
        return 2*quad(lambda z: (radius**2+z*z)**-4, 0., half_length,
                      epsabs=1e-15, epsrel=1e-13)[0]
    rows = []
    for ratio in (.25, 1., 4.):
        area = 2*quad(lambda t: (1+t*t)**-4, 0., ratio)[0]
        slope = 7+2*ratio/((1+ratio**2)**4*area)
        step = 2e-5
        measured = (math.log(response(math.exp(-step), ratio))-
                    math.log(response(math.exp(step), ratio)))/(2*step)
        assert 7 < slope < 8 and abs(slope-measured) < 2e-9
        rows.append(dict(half_length_over_distance=ratio, log_slope=slope, radial_difference=measured))
    length, impact = 5., 1.3
    def images(y):
        return point_prefactor*sum((impact**2+(y+j*length)**2)**-4 for j in range(-40, 41))
    zero = quad(images, -length/2, length/2, epsabs=1e-15)[0]/length
    expected = 15/(32*math.pi**4*impact**7*length)
    assert abs(zero/expected-1) < 5e-14
    return dict(finite_line=rows, zero_mode=zero, reduced_green_over_length=expected)


def circle_coupling_checks():
    # Disjoint packets of fixed physical support on larger and larger circles.
    grid_step = .01
    rows = []
    for length in [16., 32., 64., 128.]:
        y = np.arange(-length/2, length/2, grid_step)
        def packet(center):
            width = 1.
            u = np.maximum(1-((y-center)/width)**2, 0.)**3
            return u/np.sqrt(grid_step*(u @ u))
        a, b = packet(-1.4), packet(1.4)
        assert np.max(abs(a*b)) == 0.
        # Unit-mass Gaussian kernel of fixed physical width, periodized explicitly.
        delta = np.arange(len(y))*grid_step
        kernel = sum(np.exp(-.5*((delta+j*length)/2.)**2) for j in range(-3, 4))/(2*math.sqrt(2*math.pi))
        assert abs(grid_step*sum(kernel)-1) < 4e-14
        bfss = sum(15*2.**6/(16*(2.**2+(delta+j*length)**2)**3.5) for j in range(-48, 49))
        assert abs(grid_step*sum(bfss)-1) < 3e-13
        def nonlocal_energy(field, physical_kernel):
            squared = field**2
            if physical_kernel is None:
                convolution = np.full(len(y), grid_step*sum(squared)/length)
            else:
                convolution = grid_step*np.fft.irfft(np.fft.rfft(physical_kernel)*np.fft.rfft(squared), n=len(y))
            return grid_step*(squared @ (squared-convolution))/2
        def mixed(physical_kernel):
            return 4*(nonlocal_energy(a+b, physical_kernel)-nonlocal_energy(a, physical_kernel)-nonlocal_energy(b, physical_kernel))
        flat_mixed, finite_range, matrix_shape = mixed(None), mixed(kernel), mixed(bfss)
        assert abs(flat_mixed+4/length) < 3e-13
        rows.append(dict(circumference=length, constant_kernel_quartic=flat_mixed,
                         physical_range_quartic=finite_range, bfss_shape_quartic=matrix_shape))
    assert abs(rows[-1]["physical_range_quartic"]-rows[-2]["physical_range_quartic"]) < 3e-12
    assert abs(rows[-1]["physical_range_quartic"]) > .1
    assert abs(rows[-1]['bfss_shape_quartic']-rows[-2]['bfss_shape_quartic']) < 3e-9
    return rows
