"""Outgoing dipole, free surface, charge-to-two-photon channel (paper 2, Z.14).

c=hbar=1. All integrations are deterministic. A complex classical amplitude
represents the sum of stresses of two real quadratures. It is not a photon.
"""
import argparse
import json
from fractions import Fraction
from math import acosh, cosh, exp, log, pi, sinh, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.special import roots_legendre


def witness():
    d, offset = Fraction(3, 5), Fraction(13, 8)
    boost = (2*d*offset**2/(1-d**2)-d)/(1+2*offset)
    t = 1 + offset
    k = (boost+d)/2
    nu2 = t-(boost-k)**2
    inertia = offset/(t*(boost+d))
    gap_ratio = t+boost*d+(boost+d)*d/offset
    return boost, k, nu2, inertia, inertia*gap_ratio


def shape_stability():
    boost, k, n, inertia, stiffness = witness()
    t = (boost-k)**2+n
    a, b, c, d = -k, Fraction(1), (boost-k)/t, -1/t
    denominator = inertia*(a*a+n*b*b)+stiffness
    # Real coordinates are Re(a), Im(a)/nu, Re(b), Im(b)/nu.
    numerator = (a+c)**2+n*(b+d)**2+a*a+n*b*b-2
    assert numerator == boost*denominator
    grad = [(4*a+2*c-boost*2*inertia*a)/denominator,
            n*(4*b+2*d-boost*2*inertia*b)/denominator,
            2*(a+c)/denominator, 2*n*(b+d)/denominator]
    jac = np.array([
        [-1/inertia-2*a, 2*n*b, -1/inertia, 0],
        [-2*b, -1/inertia-2*a, 0, -1/inertia],
        [-c, n*d, -(a+boost), n*b],
        [-d, -c, -b, -(a+boost)]], dtype=object)
    for col in range(4):
        jac[2, col] -= c*grad[col]
        jac[3, col] -= d*grad[col]
    identity = np.eye(4, dtype=int).astype(object)
    leverrier = identity
    coefficients = []
    for order in range(1, 5):
        product = jac @ leverrier
        coeff = -sum(product.diagonal(), Fraction())/order
        coefficients.append(coeff)
        leverrier = product+coeff*identity
    assert all(x == 0 for x in leverrier.flatten())
    p, q, r, u = coefficients
    hurwitz = [p, p*q-r, (p*q-r)*r-p*p*u, u]
    assert all(h > 0 for h in hurwitz)
    eig = np.linalg.eigvals(np.asarray(jac, dtype=float))
    return dict(characteristic=[str(i) for i in coefficients],
                hurwitz=[str(i) for i in hurwitz],
                shape_eigenvalues=sorted([[float(z.real),float(z.imag)] for z in eig]),
                rapidity_eigenvalue=-sqrt(float(boost**2-1)))


def surface_run(displacement=0., substrate=0., rest=0., empty_near=False):
    boost, k, nu2, inertia, stiffness = map(float, witness())
    mode = -k + 1j*sqrt(nu2)
    velocity = -sqrt(boost*boost-1)
    theta0 = -acosh(boost)+displacement
    q0, y0 = 1+0j, mode*(1+displacement/3)
    d0 = 0j if empty_near else (1+1j*displacement)/(boost+mode)
    def energy(q, y, d, theta, lr):
        radius = exp(lr)
        b, v = cosh(theta), sinh(theta)
        h = (b-v)*d
        scaled = substrate+(inertia*abs(y)**2+stiffness*abs(q)**2)/2
        near = abs(q)**2-(q.conjugate()*h).real+abs(h)**2/2
        return b*(rest+scaled/radius)+near/radius
    def charge_norm(q, y, d, theta):
        h = exp(-theta)*d
        return inertia*(q.conjugate()*y).imag+(h.conjugate()*q).imag
    def rhs(w, state):
        q,y,d = state[:3]
        theta,lr = state[3:5].real
        b,v = cosh(theta),sinh(theta)
        radius, zeta = exp(lr),exp(-theta)
        scaled = substrate+(inertia*abs(y)**2+stiffness*abs(q)**2)/2
        pressure = (abs(y+d)**2+abs(y)**2)/2-abs(q)**2
        accel = (b*scaled-pressure)/(scaled+rest*radius)
        h = zeta*d
        wave = y-zeta*q+b*h
        return [y,-(y+stiffness*q+d)/inertia,q+(accel-b)*d,
                accel,v,abs(wave)**2/(radius*zeta),
                ((q-h).conjugate()*wave).imag, radius,radius*zeta]
    def expanded(w, state):
        return 2.0-state[3].real
    expanded.terminal = True
    initial = [q0,y0,d0,theta0,0,0,0,0,0]
    end = 16 if substrate+rest == 0 else 48
    sol = solve_ivp(rhs,(0,end),np.array(initial,complex),method="DOP853",
                    atol=2e-14,rtol=3e-12,max_step=.045,events=expanded)
    assert sol.success
    energy0 = energy(q0,y0,d0,theta0,0)
    norm0 = charge_norm(q0,y0,d0,theta0)
    local, norms = [], []
    for col in sol.y.T:
        q,y,d = col[:3]
        theta, lr = col[3:5].real
        local.append(energy(q,y,d,theta,lr))
        norms.append(charge_norm(q,y,d,theta))
    e_drift = float(max(abs(np.array(local)+sol.y[5].real-energy0))/energy0)
    n_drift = float(max(abs(np.array(norms)+sol.y[6].real-norm0)))
    assert e_drift < 2e-9 and n_drift < 2e-9
    q,y,d,theta,lr,out,phase,tau,ret = sol.y[:,-1]
    if displacement == substrate == rest == 0 and not empty_near:
        assert abs(theta.real-theta0)<1e-8 and abs(lr-velocity*end)<1e-7
        assert abs(local[-1]/energy0-exp((velocity*(-1)-2*k)*end))<1e-10
    return dict(displacement=displacement,substrate=substrate,rest=rest,empty_near=empty_near,
                end_w=float(sol.t[-1]),initial_energy=energy0,initial_norm=norm0,
                min_radius=float(np.exp(sol.y[4].real).min()),final_radius=exp(lr.real),
                final_speed=sinh(theta.real),max_energy_error=e_drift,max_norm_error=n_drift,
                outgoing_fraction=out.real/energy0,remaining_fraction=local[-1]/energy0,
                final_norm=norms[-1],proper_time=tau.real,retarded_time=ret.real,
                final_shape_distance=abs(y/q-mode)+abs(d/q-1/(boost+mode)) if abs(q)>1e-18 else None)


def quantum(boost, inertia, stiffness, delta=1., coupling=.25):
    def rho(x):
        damping = x*(boost*boost-1+x*x)/(boost*boost+x*x)
        detuning = stiffness-inertia*x*x+boost/(boost*boost+x*x)
        return damping/(pi*(detuning**2+damping**2))
    def pairs(energy):
        return energy*quad(lambda t:rho(t*energy)*rho((1-t)*energy),
                           0,1,epsabs=1e-30,epsrel=2e-11,limit=120)[0]
    moment0 = quad(lambda x:rho(x)/x,0,np.inf,epsabs=2e-12)[0]
    moment1 = quad(lambda x:x*rho(x),0,np.inf,epsabs=2e-12)[0]
    assert abs(moment0-.5/(stiffness+1/boost))<5e-11
    assert abs(moment1-.5/inertia)<5e-11
    # Two independent quadrature orders, compactifying each half-line.
    def integral(order):
        z, weights = roots_legendre(order)
        nodes = (1+z)/(1-z)
        measure = weights*2/(1-z)**2*rho(nodes)
        return float(np.sum(np.outer(measure,measure)/(nodes[:,None]+nodes[None,:])))
    previous, shift = integral(160),integral(256)
    bound = 1/(8*sqrt(inertia)*(stiffness+1/boost)**1.5)
    assert abs(previous-shift)<1e-9 and 0<shift<bound and coupling**2*bound<delta
    power = 3 if boost>1 else 7
    coeff = ((1-1/boost**2)**2/(6*pi*pi*(stiffness+1/boost)**4) if boost>1
             else 1/(140*pi*pi*(stiffness+1)**4))
    assert abs(pairs(.0001)/(.0001**power*coeff)-1)<1e-6
    density = [[x,pairs(x)] for x in [.0001,.01,.1,1.,2*sqrt(stiffness/inertia)]]
    gap0 = delta-coupling**2*shift
    from math import factorial
    tail = (factorial(power)*coupling**2*coeff/gap0**2)**2
    return dict(boost=boost,moments=[moment0,moment1],threshold_power=power,
                threshold_coefficient=coeff,pair_spectrum=density,
                reference_gap=delta,reference_coupling=coupling,
                golden_rate_per_w=2*pi*coupling**2*pairs(delta),
                shift_integral=shift,shift_bound=bound,threshold_gap=gap0,
                tail_probability_coefficient=tail,
                log_asymptotic_charge_energy=[(w,log(delta*tail)-(2*power+2)*log(w)
                                                    +sqrt(boost**2-1)*w) for w in [100,500,1000]])


def angular_channel():
    eye = np.eye(3)
    tensors = [np.diag([1,-1,0])/sqrt(2),np.diag([1,1,-2])/sqrt(6)]
    for i,j in [(0,1),(0,2),(1,2)]:
        tensors.append((np.outer(eye[i],eye[j])+np.outer(eye[j],eye[i]))/sqrt(2))
    basis = np.asarray(tensors).reshape(5,9)
    gram = basis @ basis.T
    assert np.max(abs(gram-np.eye(5)))<4e-15
    # Entanglement fidelity of a uniform rank-five input, after discarding
    # the gravitational record. Equal marks preserve all coherences.
    return dict(pair_gram_error=float(abs(gram-np.eye(5)).max()),
                common_mark_entanglement_fidelity=float(np.ones((5,5)).sum()/25),
                resolved_marks_entanglement_fidelity=float(np.eye(5).sum()/25))


def charged_equilibrium():
    from scipy.optimize import brentq
    # Multiply the second variation of the ADM energy by 4(1-x)^2 R^2/m.
    def stability(x):
        return 8*(1-x)**3-x*(2-x)**2
    boundary = brentq(stability, .4, .6)
    rows = []
    for x in [.02, .25, 1-1/sqrt(3), .45, .48, .50, .64]:
        fraction = (4-3*x)/(6*(1-x))
        mu = 1-x/2
        def adm(y):
            proper = fraction/y+(1-fraction)*y*y
            return proper*(1-x*proper/(2*y))
        h = .0001
        curvature = (adm(1+h)+adm(1-h)-2*adm(1))/h**2
        exact = stability(x)/(4*(1-x)**2)
        assert abs((adm(1+h)-adm(1-h))/(2*h))<1e-7 and abs(curvature-exact)<2e-6
        # y=1/(1-z^2) removes both square-root endpoints. Work with
        # (F-1)/(y-1) directly near rest to avoid cancellation.
        def retarded(z):
            y = 1/(1-z*z)
            slope = mu-x*(y+1)/(2*y*y)
            boost = mu*y+x/(2*y*y)
            speed = sqrt(slope*y*(boost+1))*z
            boost_out = boost-x/(y*y)
            return 2*y*y/(sqrt(slope*y*(boost+1))*(boost_out+speed))
        lag = quad(retarded,0,1,epsabs=2e-12,epsrel=2e-12)[0]
        rows.append(dict(proper_compactness=x,external_compactness=2*x-x*x,
                         winding_fraction=fraction,dimensionless_second_derivative=exact,
                         stable=bool(exact>0),retarded_flight_over_radius=lag,
                         local_pair_wavelength_test_mass_times_radius=1/fraction,
                         infinity_gap_times_radius_for_unit_winding=mu/fraction))
    assert abs(quad(lambda z:2/(sqrt(2-z*z)*(1+z*sqrt(2-z*z))),0,1)[0]-1)<2e-12
    return dict(positive_tension_upper=2/3,radial_stability_upper=boundary,
                photon_sphere_x=1-1/sqrt(3),cases=rows)


def surface_flux():
    from math import asinh, atan, ceil, cos, sin
    from scipy.optimize import brentq
    stellar_time = 3*4.925490947  # GM/c^3 in microseconds
    cap = 9/8
    radius_time = 2*stellar_time*cap
    proper = sqrt(1-1/cap)*2*stellar_time*quad(lambda y:y/(1+sqrt(y)),cap,1.5)[0]
    angle = proper/radius_time
    area = sin(angle/2)**2
    rows = []
    for a in [.03,.1,.5,1.,3.]:
        turn = 2*atan(a)
        # Evaluate the momentum in the forbidden cap; normalize by eta*R^2.
        def barrier(th):
            return sqrt(max(0.,sin(th)**2-4*sin(th/2)**4/a**2))
        bounce = 4*pi*quad(barrier,0,turn,epsabs=3e-14,epsrel=1e-12)[0]
        analytic = 8*pi*(1-asinh(a)/(a*sqrt(1+a*a)))
        assert abs(bounce/analytic-1)<1e-10
        sweep = quad(lambda phi:2*a/(a*a+sin(phi)**2),0,pi/2)[0]
        assert abs(sweep-pi/sqrt(1+a*a))<3e-12
        rows.append(dict(wall_ratio=a,neutral_turn_angle=turn,bounce_over_line_tension_radius_squared=bounce,
                         bounce_over_flat=bounce/(16*pi*a*a/3),sweep_over_radius=sweep,
                         charged_write_barrier_over_2pi_sigma_R2=1+sqrt(1+a*a)))
    x = .25
    af = (4-3*x)/(6*(1-x))
    ratio = brentq(lambda y:x*(af/y**2+(1-af)*y)-2/3,1,20)
    lin = (1+x/(2*(1-x)))/2
    # Optimistic cost for a locally written patch. Its area is pi times
    # chord radius squared. The freely falling body has gamma=3 here.
    grav, light = 6.67430e-11, 299792458.
    radius_m = radius_time*299.792458
    strength = x*(1-lin)
    patch_examples = []
    for mass, chord in [(70.,.5),(1.31e-9,5.e-5)]:
        available = mass/sqrt(1-1/cap)
        mass_cost = strength*light**2*chord**2/(4*grav*radius_m)
        affordable = sqrt(4*grav*radius_m*available/(strength*light**2))
        patch_examples.append(dict(body_mass_kg=mass,assumed_contact_chord_m=chord,
                                   material_surface_cost_in_kg=mass_cost,
                                   maximum_chord_from_infall_energy_m=affordable))
    # Two degenerate flux orientations differ only along a string wall.
    # On a fixed sphere, E=2*pi*eta*R*sin(theta)/sqrt(1-R^2 theta_dot^2).
    # Integrate to the turning point with sin(theta)=k*sin(phi); K is complete.
    from scipy.special import ellipk
    kturn = brentq(lambda k:k*ellipk(k*k)-angle,1.e-8,.25)
    eta = 1.054571817e-34*light/(1.e-9)**2  # a material example, in J/m
    turning_time = radius_time*quad(lambda phi:kturn/sqrt(1-kturn**2*sin(phi)**2),
                                    0,pi/2)[0]
    assert abs(turning_time-proper)<5e-12
    orientation = dict(sin_turn_angle=kturn,maximum_transverse_radius_m=kturn*radius_m,
                       turnaround_us=turning_time,collapse_us=2*turning_time,
                       illustrative_string_tension_joule_per_m=eta,
                       seed_energy_joule=2*pi*eta*kturn*radius_m,
                       available_till_return_after_turn_us=turning_time)
    # Winding captured at maximum radius gives two turning points; on a
    # fixed sphere the null speed around a freely collapsing bare string is
    # exactly 1/(R*kturn). A light signal from the central port catches it first.
    from scipy.special import ellipkinc
    from math import asin
    def fall_to(theta):
        return kturn*(ellipk(kturn*kturn)-
                      ellipkinc(asin(min(1.,sin(theta)/kturn)), kturn*kturn))
    meet = brentq(lambda theta:fall_to(theta)-theta,0,asin(kturn))
    angle_left = (angle-meet)/kturn
    orientation["central_receipt_to_rim_us"] = meet*radius_time
    orientation["remaining_azimuth_rad"] = angle_left
    orientation["minimum_simultaneous_rim_sites"] = ceil(pi/angle_left)
    pinned = []
    for small in [.5,50.e-6]:
        def transit(big):
            modulus = (big*big-small*small)/(radius_m**2-small*small)
            return (big+small)*ellipk(modulus)/sqrt(1-(small/radius_m)**2)
        big = brentq(lambda turning:transit(turning)-proper*299.792458,small,2000.)
        # f=1; N=n^2. Round up only for the minimum winding count.
        winding = 2*pi*eta*big*small/(1.054571817e-34*light)
        bareturn = kturn*radius_m
        pinned.append(dict(minimum_radius_m=small,maximum_radius_m=big,required_N=winding,
            minimum_integer_winding=ceil(sqrt(winding)),inverse_fermi_wave_number_m=small/sqrt(winding),
            minimum_channels_for_nm_core=ceil(winding*(1.e-9/small)**2),seed_energy_joule=2*pi*eta*(big+small),
            single_winding_min_radius_after_capture_m=1.054571817e-34*light/(2*pi*eta*bareturn),
            ideal_deposit_at_bare_turn_joule=2*pi*eta*small))
    orientation["winding_supported"] = pinned
    return dict(boundary_clock_us=proper,radius_over_c_us=radius_time,
        antipodal_delay_us=pi*radius_time,max_angle=angle,max_arc_metres=proper*299.792458,
        max_area_fraction=area,minimum_simultaneous_seeds=ceil(1/area),
        flux_caps=rows,constant_tension_max_radius_ratio_at_x_quarter=ratio,
        line_energy_asymptotic_proper_compactness=x*(1-lin),
        line_max_asymptotic_proper_compactness=1-sqrt(3)/2,
        line_max_asymptotic_external_compactness=.25,local_patch_costs=patch_examples,degenerate_orientation=orientation)


def irreversible_check():
    speed = sqrt(float(witness()[0]**2-1))
    # E0=4 Delta/R_i. Even a large mean rate leaves an over-budget history.
    rows = []
    for multiple in [.8,1.,2.,5.,10.]:
        rate = multiple*speed
        rows.append(dict(hazard_over_speed=multiple,finite_mean=bool(rate>speed),
                         mean_energy_over_initial_gap=rate/(rate-speed) if rate>speed else None,
                         survival_at_budget=exp(-rate*log(4)/speed)))
    return rows


def quantum_rim():
    from scipy.linalg import eigh_tridiagonal
    from scipy.special import eval_genlaguerre, gammainc, gammaln
    rows = []
    for winding_weight in [1,4,16,64]:
        alpha = sqrt(winding_weight**2+.25)
        at = .5*sqrt(winding_weight)
        # a0=A/(hbar*c)=1. Test eigenenergies via an independent finite-difference
        # Friedrichs operator, using Dirichlet endpoints well beyond the test code.
        end = 2*sqrt(winding_weight)+12
        spacings = []
        for cells in [1400,2800]:
            dr = end/(cells+1)
            grid = dr*np.arange(1,cells+1)
            diag = 2/dr**2+(grid+winding_weight/grid)**2
            computed = eigh_tridiagonal(diag,np.full(cells-1,-1/dr**2),
                                         select="i",select_range=(0,4),eigvals_only=True)
            exact = np.arange(5)*4+2+2*alpha+2*winding_weight
            spacings.append(float(max(abs(computed-exact))))
        assert spacings[1]<.002 and spacings[1]<.35*spacings[0]
        density = lambda z,n: (exp(gammaln(n+1)-gammaln(n+alpha+1)
                                    +alpha*log(z)-z)*eval_genlaguerre(n,alpha,z)**2
                                if z>0 else 0.)
        probs = [quad(lambda z:density(z,n),0,at**2,epsabs=1.e-100,epsrel=5e-11)[0]
                 for n in [0,1,4]]
        assert 0<probs[0] and abs(probs[0]/gammainc(alpha+1,at**2)-1)<2e-12
        assert abs(quad(lambda z:density(z,4),0,np.inf,limit=180)[0]-1)<1e-10
        rows.append(dict(winding_weight=winding_weight,ground_probability_inside_half_equilibrium=probs[0],
                         probability_for_n_one=probs[1],probability_for_n_four=probs[2],
                         finite_difference_eigenenergy_squared_errors=spacings))
    return rows


def thermal_winding(surface):
    # Conditional benchmark: independent conserved axial windings in a Gibbs
    # state, with a quadratic integer spectrum. Optical modes with no protected
    # charge need not retain their pressure after the material has been captured.
    boltzmann, temp, light, hbar = 1.380649e-23,300.,299792458.,1.054571817e-34
    columns = surface["degenerate_orientation"]
    tension = columns["illustrative_string_tension_joule_per_m"]
    examples = []
    for case in columns["winding_supported"]:
        small = case["minimum_radius_m"]
        target = 2*pi*tension*case["maximum_radius_m"]
        qval = hbar*light/(small*boltzmann*temp)
        cutoff = int(np.ceil(sqrt(80/qval)))
        integers = np.arange(-cutoff,cutoff+1,dtype=float)
        weights = np.exp(-qval*integers**2)
        mean = qval*np.dot(integers**2,weights)/sum(weights)
        assert mean<=.5+2e-13 and abs(mean-.5)<2e-12
        examples.append(dict(min_radius=small,thermal_ratio=qval,mean_work_per_kBT=mean,
                             individual_zero_probability=1/sum(weights),
                             required_channels_for_mean=2*target/(boltzmann*temp),
                             initial_winding_energy_J=target))
    avogadro = 6.02214076e23
    atoms = int(3*1.31e-9/.0600843*avogadro)
    ratio = examples[1]["required_channels_for_mean"]/atoms
    assert ratio>1
    return dict(temperature_K=temp,examples=examples,
                illustrative_silica_atom_count=atoms,ratio_to_equipartition=ratio,
                log10_chernoff_bound=-atoms*.5*(ratio-1-log(ratio))/log(10))


def constrained_ports():
    from itertools import combinations_with_replacement
    # Each port carries four arbitrary code modes, including opposite ordinary
    # charges. Cut off total occupation only for a check of the all-Fock rule.
    occupations = []
    for n in range(4):
        for labels in combinations_with_replacement(range(8),n):
            occupations.append(tuple(labels.count(i) for i in range(8)))
    indices = {state:i for i,state in enumerate(occupations)}
    swap = np.array([indices[s[4:]+s[:4]] for s in occupations])
    source = np.asarray(occupations)
    left, right = source[:,:4],source[:,4:]
    kept_a = right.sum(axis=1)==0
    kept_b = left.sum(axis=1)==0
    assert np.all(kept_b[swap]==kept_a) and np.all(swap[swap]==np.arange(len(swap)))
    assert not np.any(left[kept_b]) and kept_a.sum()==kept_b.sum()==35
    charge = left @ np.array([1,-1,1,-1])
    neutral_pairs = (charge==0)&(left.sum(axis=1)>0)&(right.sum(axis=1)==0)
    assert neutral_pairs.any() and not np.any(kept_b[neutral_pairs])
    energies = np.array([.8,1.,1.2,1.6])
    incoming = left @ energies
    matched = (right @ energies)[swap]-incoming
    detuned = (right @ (energies+np.array([0.,.02,0.,0.])))[swap]-incoming
    return dict(total_basis=len(occupations),physical_basis_each=int(kept_a.sum()),
                neutral_ordinary_inputs_excluded_in_b=int(neutral_pairs.sum()),
                matched_work=float(abs(matched[kept_a]).max()),
                detuned_work_range=[float(detuned[kept_a].min()),float(detuned[kept_a].max())])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",nargs="?",type=Path,default=Path(__file__).resolve().parents[1]/"verification"/"material-dipole-surface-results.json")
    path = parser.parse_args().output
    b,k,n,inertia,stiffness = witness()
    speed = sqrt(float(b*b-1))
    flux = surface_flux()
    report = dict(rational_witness=dict(boost=str(b),decay=str(k),nu_squared=str(n),
                                        inertia=str(inertia),stiffness=str(stiffness),
                                        gap_ratio=str(stiffness/inertia)),speed=speed,
                  energy_radius_power=2*float(k)/speed-1,
                  curvature_radius_power=2*float(k)/speed-4,
                  stability=shape_stability(),
                  evolutions=[surface_run(),surface_run(.015),surface_run(-.015),
                              surface_run(substrate=.001),surface_run(rest=.003),
                              surface_run(empty_near=True)],
                  quantum=[quantum(float(b),float(inertia),float(stiffness)),
                           quantum(1.,float(inertia),float(stiffness))],
                  angular=angular_channel(),charged_equilibrium=charged_equilibrium(),
                  surface_flux=flux,irreversible_jump=irreversible_check(),quantum_rim=quantum_rim(),
                  thermal_winding=thermal_winding(flux),constrained_ports=constrained_ports())
    path.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print(path.name)
