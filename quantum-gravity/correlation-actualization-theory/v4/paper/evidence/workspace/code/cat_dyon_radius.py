"""Reproduce the static orbital trace, rotating modes and charged torus comparison."""
from itertools import combinations, permutations
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import block_diag, expm, eigvalsh, null_space
from scipy.special import xlogy

from cat_magnetic_orbifold import numerical_hessian, potential


def rotation(order, flux):
    """Use the parent quartic for the real Hessian and the eight physical wave coordinates."""
    cycle = np.roll(np.eye(3), 1, axis=0).astype(complex)
    z3 = np.exp(2j * np.pi / 3)
    phase = np.diag(z3 ** np.arange(3))
    axes = [np.linalg.matrix_power(phase, j) / np.sqrt(3) for j in (1, 2)]
    axes += [np.linalg.matrix_power(phase, j) @ cycle.conj().T / np.sqrt(3) for j in (1, 2)]
    axes = np.array(axes + [1j * a for a in axes]) / np.sqrt(2)
    y2 = 8 * np.sin(np.pi * flux / order)**2 / 3
    omega2, vector2 = 2 * y2, 6.
    omega, x = np.sqrt(omega2), y2 / vector2
    v = lambda z: potential(order, np.arange(3), z, flux=flux)
    def energy(h):
        return v(cycle + np.tensordot(h, axes, axes=1))
    # All components of the complex field, including those outside the retained wave.
    units = np.eye(9).reshape(9, 3, 3)
    for shift in np.concatenate([units, 1j * units]):
        eps = .0001
        derivative = (v(cycle+eps*shift)-v(cycle-eps*shift))/(2*eps)
        assert np.isclose(derivative, 2*omega2*np.vdot(cycle,shift).real, atol=5e-7)
    for gen in np.eye(3):
        gauge = 1j*(np.diag(gen) @ cycle - cycle @ np.diag(gen))
        assert np.max(np.abs(axes.conj().reshape(8,9) @ gauge.ravel())) < 1e-13
    hess = numerical_hessian(energy, np.zeros(8), .00045)
    rows = np.column_stack((axes.real.reshape(8,9),axes.imag.reshape(8,9))) * np.sqrt(2.)
    complement = null_space(rows)
    def full_energy(h):
        return v(cycle+(h[:9]+1j*h[9:]).reshape(3,3)/np.sqrt(2.))
    whole = numerical_hessian(full_energy,np.zeros(18),.00045)
    assert np.allclose(rows@whole@rows.T,hess,atol=1e-6)
    assert np.max(np.abs(rows@whole@complement))<1e-6
    a = vector2 - 2*y2
    b = np.sqrt(a*y2)
    rot = np.block([[np.zeros((4,4)),-np.eye(4)],[np.eye(4),np.zeros((4,4))]])
    assert np.allclose(eigvalsh(hess), [a-b]*4+[a+b]*4, atol=3e-6)
    assert np.max(np.abs((hess-a*np.eye(8))@rot+rot@(hess-a*np.eye(8)))) < 5e-6
    kopt = omega2-a-b*b/(4*omega2)
    peaks = []
    for k2 in (0., max(0., kopt), .53*vector2, 1.7*vector2):
        matrix = np.block([[np.zeros((8,8)),np.eye(8)],
                           [-(hess+(k2-omega2)*np.eye(8)),-2*omega*rot]])
        poles = np.linalg.eigvals(matrix)
        roots = k2+a+omega2 + np.array([-1.,1.])*np.sqrt(4*omega2*(k2+a)+b*b)
        assert np.max(np.min(np.abs(-poles[:,None]**2-roots),axis=1)) < 1e-5
        growth = np.sqrt(max(0.,-roots[0])/vector2)
        assert abs(np.max(poles.real)/np.sqrt(vector2)-growth) < 2e-6
        peaks.append(growth)
    return dict(N=order, p=flux, x=x, k2_band_in_vector_units=[(omega2-a-b)/vector2,
                (omega2-a+b)/vector2], optimal_k2_over_vector2=max(0.,kopt/vector2),
                uniform_growth_over_vector=round(peaks[0],7), maximum_growth_over_vector=peaks[1])


def orbital():
    """S3 permutes an oriented root triangle. Two of the four fibers have the sign character."""
    roots = (np.eye(3) - np.roll(np.eye(3), -1, axis=0)) / np.sqrt(2)
    points = np.concatenate([r*roots for r in (1,2,2,3)])
    masses = np.sum((points[:,None]-points[None,:])**2, axis=2).ravel()
    id_space = len(masses)
    vector_proj = np.zeros((id_space,id_space))
    spin_proj = np.zeros((4*id_space,4*id_space))
    for perm in permutations(range(3)):
        raw = np.eye(3)[list(perm)]
        sign = int(round(np.linalg.det(raw)))
        coordinates = sign*raw
        target = np.argmin(np.linalg.norm((roots@coordinates.T)[:,None]-roots[None,:],axis=2),axis=1)
        r3 = np.eye(3)[:,target]
        assert np.allclose(roots@coordinates.T, roots[target])
        fibers = block_diag(r3,sign*r3,sign*r3,r3)
        adjoint = np.kron(fibers,fibers)
        vector_proj += adjoint/6
        spin_proj += np.kron(block_diag(1., coordinates),adjoint)/6
    assert np.allclose(vector_proj@vector_proj,vector_proj) and np.allclose(spin_proj@spin_proj,spin_proj)
    weights = spin_proj.diagonal().reshape(4,-1).sum(axis=0)/4-vector_proj.diagonal()
    assert abs(sum(weights))<1e-11 and abs(weights@masses)<1e-11
    for s in (.03,.2,1.,7.):
        assert np.isclose(weights@np.exp(-s*masses),-(6-8*np.exp(-s)+2*np.exp(-4*s))/2)
    coefficient = 2*weights@xlogy(masses,masses)
    # expm1 cancels the constant terms at the lower integration endpoint.
    integral = quad(lambda t: (8*np.expm1(-t)-2*np.expm1(-4*t))/t**2,0,np.inf)[0]
    assert np.isclose(coefficient,integral) and np.isclose(coefficient,-8*np.log(4))
    return dict(vector_count=round(vector_proj.trace()),weyl_count=round(spin_proj.trace()),
                response=coefficient,independent_integral=integral)


def torus_fields(h):
    """At the origin h[:36] = delta G + B, h[36] = axion/s*, h[37] = log(s/s*)."""
    shift = h[:36].reshape(6,6)
    sym = (shift+shift.T)/2
    # exp of a symmetric generator keeps arbitrary test displacements in the physical cone.
    geometry = expm(sym)
    return geometry,(shift-shift.T)/2


def charge_masses(h,k=3.,l=1.,check=False,fragments=False):
    geometry,bfield = torus_fields(h)
    inverse = np.linalg.inv(geometry)
    saxion = (k/l)*np.exp(h[37])
    axion = (k/l)*h[36]
    eye = np.eye(6)
    masses = []
    for i in (0,2,4):
        axes = eye[:,[i,i+1]] * np.array([k,l])
        right = (eye-bfield+geometry) @ axes
        gram = right.T@inverse@right
        if check:
            left = (eye-bfield-geometry) @ axes
            assert np.allclose(gram-left.T@inverse@left,4*np.diag([k*k,l*l]))
        trace = (gram[0,0]-2*axion*gram[0,1]+(axion**2+saxion**2)*gram[1,1])/saxion
        bound = np.sqrt(trace+2*np.sqrt(np.linalg.det(gram)))
        separate = (np.sqrt(gram[0,0])+np.hypot(axion,saxion)*np.sqrt(gram[1,1]))/np.sqrt(saxion)
        if check:
            assert separate>=bound-1e-12
        masses.append((separate if fragments else bound)/(4*np.sqrt(k*l)))
    return np.array(masses)


def fixed_charges(rng):
    weights = np.array([.2,.3,.5])
    center = np.zeros(38)
    assert np.allclose(charge_masses(center),1)
    for _ in range(120):
        points = .3*rng.normal(size=38)
        assert np.min(charge_masses(points,check=True)) >= 1
    # The sigma model gives M_P times h_ij/2, and M_P times z/sqrt(2) for each axion-dilaton coordinate.
    canonical = np.r_[[2.]*36,[np.sqrt(2)]*2]
    def density(fields):
        return weights@charge_masses(fields*canonical)
    spectrum = np.sort(np.r_[np.tile(np.repeat(weights,2),6)/2,[.5,.5]])
    errors = []
    for step in (.0008,.0004):
        numerical = eigvalsh(numerical_hessian(density,center,step))
        errors.append(float(np.max(np.abs(numerical-spectrum))))
    assert max(errors)<2e-6
    fragment_hessian = numerical_hessian(lambda h: weights@charge_masses(h*canonical,fragments=True),
                                         center,.0004)
    extra_axion = np.zeros((38,38))
    extra_axion[36,36] = .5
    assert np.allclose(fragment_hessian-extra_axion,
                       np.diag(np.r_[np.tile(np.repeat(weights,2),6)/2,[.5,.5]]),rtol=0.,atol=1e-6)
    # Removing a species leaves the two uncovered columns free, at finite amplitude.
    test = rng.normal(size=(6,2))*.01
    metric = np.eye(6)
    shear = np.zeros((6,6))
    shear[:,4:] = test
    metric += (shear+shear.T)/2
    vals, vecs = np.linalg.eigh(metric)
    gen = (vecs*np.log(vals))@vecs.T+(shear-shear.T)/2
    assert np.allclose(charge_masses(np.r_[gen.ravel(),0.,0.])[:2],1.,atol=1e-13)
    return dict(fractions=weights.tolist(),canonical_mass2_over_density_mplminus2=[
        [float(v),int(np.count_nonzero(spectrum==v))] for v in np.unique(spectrum)],
        hessian_error_tolerance=2e-6,fragment_axion_mass2_over_density_mplminus2=round(fragment_hessian[36,36],5),
        missing_one_species_flat_directions=12)


def three_form_slope(rng):
    # Real part of (dx1+i dx2)(dx3+i dx4)(dx5+i dx6), in exterior-product normalization.
    triples = list(combinations(range(6),3))
    form = np.zeros(len(triples))
    for i in (0,1):
        for j in (0,1):
            for k in (0,1):
                form[triples.index((i,2+j,4+k))]=(1j**(i+j+k)).real
    nonzero = np.flatnonzero(form)
    def norm(metric):
        inverse = np.linalg.inv(metric)
        total = sum(form[i]*form[j]*np.linalg.det(inverse[np.ix_(triples[i],triples[j])])
                    for i in nonzero for j in nonzero)
        return np.sqrt(np.linalg.det(metric))*total
    assert norm(np.eye(6))==4.
    eps = .0001
    slopes=[]
    for i in range(6):
        for j in range(i+1):
            direction=np.zeros((6,6))
            direction[i,j]=direction[j,i]=1
            slopes.append((norm(expm(eps*direction))-norm(expm(-eps*direction)))/(2*eps))
    assert max(map(abs,slopes))<1e-8
    trials=[]
    for _ in range(12):
        h=rng.normal(size=(6,6))
        metric=expm(.1*(h+h.T))
        trials.append(norm(metric))
        assert np.isclose(norm(metric),norm(1.7*metric))
    least_ratio = np.inf
    for _ in range(120):
        radii = np.exp(rng.uniform(-3,3,6))
        coefficients = rng.integers(1,9,size=4)
        terms = np.array([c*np.sqrt(np.prod(radii))/np.prod(radii[list(triples[i])])
                          for c,i in zip(coefficients,nonzero)])
        assert np.isclose(np.prod(terms),np.prod(coefficients))
        ratio = np.sum(terms)/(4*np.prod(coefficients)**.25)
        least_ratio = min(least_ratio,ratio)
        assert ratio>=1-1e-13
    return dict(squared_norm=4,max_abs_linear_metric_slope=max(map(abs,slopes)),
                least_deformed_sample=min(trials),single_coordinate_D3_mass_over_MPl=np.sqrt(np.pi),
                calibrated_line_mass_lower_bound_over_MPl=4*np.sqrt(np.pi),
                rectangular_min_ratio_in_samples=least_ratio)


def laboratory():
    def em(z,a):
        return 1e-4*(-1.4+8.2*z/a+7.7*z*(z-1)/a**(4/3))
    alloy_ti = .9*em(22,47.867)+.06*em(13,26.982)+.04*em(23,50.942)
    alloy_pt = .9*em(78,195.084)+.1*em(45,102.906)
    sil = (28.085*em(14,28.085)+2*15.999*em(8,15.999))/(28.085+2*15.999)
    earth = .32*em(26,55.845)+.68*sil
    eta = 4*earth*(alloy_ti-alloy_pt)
    envelope = (1.5+1.96*np.hypot(2.3,1.5))*1e-15
    slope_limit = np.sqrt(envelope/(2*earth*abs(alloy_ti-alloy_pt)))
    return dict(earth_Q=earth,titanium_Q=alloy_ti,platinum_Q=alloy_pt,eta=eta,
                normal_95_envelope=envelope,canonical_em_slope_limit=slope_limit,
                ratio_to_envelope=abs(eta)/envelope,one_stack_min_bare_alpha=1/(137.036*slope_limit/np.sqrt(2)),
                many_stacks_min_charge_weighted_alpha=1/(137.036*slope_limit*np.sqrt(2)))


def nuclear_running():
    """Common DBI gauge function for light electromagnetism and an asymptotically free color group."""
    weights_ti=[(.90,22,47.867),(.06,13,26.982),(.04,23,50.942)]
    weights_pt=[(.90,78,195.084),(.10,45,102.906)]
    silica_mass = 28.085+2*15.999
    weights_earth=[(.32,26,55.845),(.68*28.085/silica_mass,14,28.085),
                   (.68*2*15.999/silica_mass,8,15.999)]
    def charges(material,surface):
        result=np.zeros(2)
        for weight,z,a in material:
            coulomb=z*(z-1)/a**(4/3)
            mean=.093-.036*surface/a**(1/3)-.020*((a-2*z)/a)**2-.00014*coulomb
            diff=.0017*(a-2*z)/a
            electron=.00055*z/a
            em=.0001*(-1.4+8.2*z/a+7.7*coulomb)
            result+=weight*np.array([mean+diff+electron,em])
        return result
    def study(surface):
        materials=[weights_ti,weights_pt,[(1.,4,9.0122)],[(1.,22,47.867)],weights_earth]
        vals=np.array([charges(m,surface) for m in materials])
        assert np.all((vals[:,0]>0)&(vals[:,0]<1)&(vals[:,1]>0)&(vals[:,1]<.01))
        delta=np.array([vals[0]-vals[1], vals[2]-vals[3]])
        slopes=-delta[:,0]-delta[:,1]
        intercepts=delta[:,1]
        determinant=slopes[1]*intercepts[0]-slopes[0]*intercepts[1]
        lower=abs(determinant)/(2.01*sum(abs(slopes)))
        def signals(run):
            t=(1-vals[:,0])*run+vals[:,1]
            return [(t[i]-t[j])/(.5*(t[i]+t[j])+(2+t[-1])/(1+4*t[-1]))
                    for i,j in ((0,1),(2,3))]
        for running in np.r_[0,np.logspace(-4,4,81)]:
            assert max(abs(v) for v in signals(running)) >= lower
        return dict(surface_coefficient_factor=surface,matched_roots=(delta[:,1]/delta[:,0]).tolist(),
                    max_eta_lower_bound=lower,signals_at_5=signals(5.),signals_at_25=signals(25.))
    return [study(value) for value in (.9,1.,1.1)]


def cosmology():
    """Equal abundances, fixed axiodilaton at its extremum, and cold comoving particles."""
    matter, equality = .315, 3402.
    radiation = matter/(1+equality)
    vacuum = 1-matter-radiation
    runs = []
    for fraction in (.1,.5,1.):
        def rhs(log_a,state):
            u,velocity = state
            a = np.exp(log_a)
            dust = matter*a**-3*(1-fraction+fraction*np.cosh(u))
            rad = radiation*a**-4
            hubble2 = (dust+rad+vacuum)/(1-velocity**2)
            dlog_h = -(1.5*dust+2*rad)/hubble2-3*velocity**2
            force = matter*fraction*a**-3*np.sinh(u)/(2*hubble2)
            return [velocity,-(3+dlog_h)*velocity-force]
        values=[]
        for tol in (2e-9,2e-11):
            solution=solve_ivp(rhs,(-np.log1p(equality),0.),[.1,0.],
                               method="DOP853",rtol=tol,atol=tol*1e-2)
            assert solution.success
            values.append(solution.y[0,-1])
        assert abs(values[0]-values[1])<1e-8
        runs.append(dict(fraction=fraction,initial_log_radius=.1,today_log_radius=values[1]))
    return runs


if __name__ == "__main__":
    rng = np.random.default_rng(12809)
    data = dict(rotation=[rotation(n,p) for n,p in ((11,1),(5,1),(5,2),(7,3),(11,5),(31,15))],
                commuting=orbital(),torus=fixed_charges(rng),rr=three_form_slope(rng),
                laboratory=laboratory(),nuclear_running=nuclear_running(),cosmology=cosmology())
    out = Path(__file__).resolve().parents[1]/"verification"/"cat-dyon-radius-results.json"
    out.write_text(json.dumps(data,indent=2,ensure_ascii=False)+"\n",encoding="utf8")
