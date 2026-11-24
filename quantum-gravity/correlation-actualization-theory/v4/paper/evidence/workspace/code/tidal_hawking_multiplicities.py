"""Tidal recoil during infall and the modes available in one Hawking history.

SI units for material transit. The radiation variable is x=hbar*omega/(k_B*T_H).
The Regge--Wheeler integrator uses omega*r_s/c=x/(4*pi).
"""
import argparse
import json
import math
from itertools import product
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.special import jv, jvp, roots_legendre, yv, yvp

from natural_flux_endpoints import tensor_scattering

ROOT = Path(__file__).resolve().parents[1]
G, C, MSUN = 6.67430e-11, 299792458., 1.98847e30


def tidal_check():
    rows = []
    for radius_ratio in (1.05, 1.3, 2.):
        ratio_power = radius_ratio**1.5
        start = ratio_power/(ratio_power-1)
        end = start-1
        y = 1/math.sqrt(radius_ratio)
        maximum = 2/(9*end**2)
        assert maximum < 1.
        for k in (0., 0.2, 1., 3., 14., 70.):
            def equation(t, flat):
                phase = flat.reshape(2, 2)
                acc = -(k*k+2/(9*(start-t)**2))*phase[0]
                return np.r_[phase[1],acc]
            solution = solve_ivp(equation, (0., 1.), np.eye(2).ravel(),
                                 method="DOP853", rtol=4e-12, atol=1e-13)
            matrix = solution.y[:,-1].reshape(2,2)
            if k:
                def frame(s):
                    arg = k*s
                    bessel = np.array([jv(1/6,arg),yv(1/6,arg)])
                    deriv = np.array([jvp(1/6,arg),yvp(1/6,arg)])
                    return np.array([math.sqrt(s)*bessel,
                                     -bessel/(2*math.sqrt(s))-k*math.sqrt(s)*deriv])
                analytic = np.linalg.solve(frame(start).T,frame(end).T).T
                reference = np.array([-k*math.sin(k), math.cos(k)])
            else:
                analytic = np.array([[2*y-y*y,3*start*(y-y*y)],
                                     [-2*(1-y)/(3*start*y*y),(2*y-1)/y**2]])
                reference = np.array([0., 1.])
            error = float(np.max(abs(analytic-matrix)))
            assert error < 1e-7 and abs(np.linalg.det(matrix)-1) < 1e-9
            rows.append(dict(outer_over_inner=radius_ratio, frequency_times_transit=k,
                             peak_tide_times_transit_squared=maximum,
                             relative_impulse=tuple(map(float,analytic[1]-reference)),
                             independent_solution_difference=error))
    times = []
    for solar in (3., 30., 4e6, 1e9):
        r_plus = 2*G*solar*MSUN/C**2
        radius = 1.05*r_plus
        w = 2*radius**1.5*math.expm1(1.5*math.log(1.3))/(3*math.sqrt(2*G*solar*MSUN))
        b = math.sqrt(r_plus/radius)
        margin = (radius-r_plus)*b/((1+b)*C)
        times.append(dict(solar_masses=solar, time_of_tidal_exchange_s=w,
                          signal_processing_margin_pg_s=margin))
    return dict(oscillators=rows, transit=times,
                sufficient_radius_ratio_upper=(1+3/math.sqrt(2.))**(2/3))


@lru_cache(maxsize=None)
def partials(x, ell_max, end_radius, order):
    result = {}
    for spin in (1,2):
        for ell in range(spin,ell_max+1):
            transmitted, reflected = tensor_scattering(x/(4*math.pi),end_radius,order,ell,spin)
            probability = abs(transmitted)**2
            assert 0 < probability <= 1+1e-8
            assert abs(probability+abs(reflected)**2-1)<2e-7
            result[spin,ell] = probability
    return result


def finite_mass_receiver():
    rows=[]
    for eta in (1.3,2.):
        a=eta**1.5/(eta**1.5-1)
        for ratio in (.01,1.,100.):
            # source mass mu=1, receiver mass m=ratio, actual reduced link mass
            kappa=ratio/(1+ratio)
            for freq in (0.,1.,9.,65.):
                def evolution(t, state):
                    q,z,v,u,impulse=state
                    tide=2/(9*(a-t)**2)
                    force=kappa*tide*(q-z)
                    return [v,u,-freq**2*q-force,force/ratio,force]
                sol=solve_ivp(evolution,(0.,1.),[0.,1.,0.,0.,0.],method="DOP853",
                              rtol=4e-12,atol=3e-14,dense_output=True)
                q,z,v,u,imp=sol.sol(np.linspace(0,1,129))
                beta=1/(9*(a-1)**2)
                assert beta<.5 and np.max(q-z)<=-1+beta/(1-beta)+1e-10
                assert imp[-1]<0 and max(abs(ratio*u-imp))<2e-13
                rows.append(dict(radius_ratio=eta,receiver_source_mass_ratio=ratio,
                            frequency_times_transit=freq,volterra_bound=beta,
                            signed_instrument_impulse=float(imp[-1]),
                            current_endpoint_error=float(max(abs(ratio*u-imp)))))
    return rows


def causal_line_receiver():
    # In units of one transit and unit source mass. Compare the emitted
    # characteristic against the empty endpoint driven by the SAME incident
    # pulse. Include radiation damping and finite receiver inertia.
    rows=[]
    for freq in (0.,1.,11.):
        for impedance in (.035,1.,15.):
            for drive in (0.,.31):
                m=.7
                reduced=m/(1+m)
                a=1.3**1.5/(1.3**1.5-1)
                def system(t,Y):
                    q,z,v,vel,empty,filtered,integral=Y
                    tide=2/(9*(a-t)**2)
                    force=reduced*tide*(q-z)
                    incoming=drive*math.sin(3*t)
                    return [v,vel,-freq**2*q-force,
                            (force+impedance*(2*incoming-vel))/m,
                            impedance*(2*incoming-empty)/m,
                            (force-impedance*filtered)/m,force]
                sol=solve_ivp(system,(0.,1.),[0.,1.,0.,0.,0.,0.,0.],method="DOP853",
                              rtol=3e-12,atol=1e-13,dense_output=True)
                q,z,v,vel,empty,filtered,integral=sol.sol(np.linspace(0,1,127))
                err=max(abs(vel-empty-filtered))
                assert err<2e-12 and (drive!=0 or max(q-z)<0 and filtered[-1]<0)
                rows.append(dict(frequency_times_transit=freq,impedance=impedance,
                                 incoming_amplitude=drive,current_filter_error=float(err),
                                 relative_outgoing_velocity=float(filtered[-1])))
    return rows


def one_energy(x):
    rates = partials(x,7,42.,9)
    counts = {(s,l):2*(2*l+1)*v for (s,l),v in rates.items()}
    total = sum(counts.values())
    reduced = sum(v for (s,l),v in counts.items() if l<=5)
    spin1_fraction = counts[1,1]/total
    q = min(1.,6*math.exp(-x))
    fidelity = 1. if spin1_fraction <= q else (
        math.sqrt(q*spin1_fraction)+math.sqrt((1-q)*(1-spin1_fraction)))**2
    return dict(x=x, effective_angular_modes=total/max(rates.values()),
                photon_dipole_fraction=spin1_fraction,
                fine_energy_reference_fidelity_upper=fidelity,
                coherent_frequency_modes_needed_in_dipole=spin1_fraction*math.exp(x)/6,
                fraction_from_wave_six_and_seven=(total-reduced)/total)


def thermal_integrals(order, ell_max, end_radius, tail_order):
    nodes, weights = roots_legendre(order)
    result = np.zeros((2,4))
    # Divide at the marked lowest-wave prohibitions and at the spectral peaks.
    # For a convergent integrated bound we count violations ONLY for l=spin.
    cuts = (0., math.log(6.),math.log(10.),4.,6.,8.,11.,16.,23.,32.,42.)
    for low, high in zip(cuts,cuts[1:]):
        for node, wnode in zip(nodes, weights):
            x = (high+low+(high-low)*node)/2
            position_weight = wnode*(high-low)/2
            for (spin,ell), trans in partials(x,ell_max,end_radius,tail_order).items():
                g = 2*(2*ell+1)
                rate = position_weight*g*trans/math.expm1(x)
                result[spin-1] += rate*np.array([1., x, math.log(g),
                                      float(ell==spin and x>math.log(g))])
    return result


def greybody():
    fine = thermal_integrals(6,5,32.,8)
    coarse = thermal_integrals(4,4,27.,7)
    rel = abs(coarse-fine)/fine
    assert np.max(rel) < 0.003
    rows = []
    for k, (number, energy, angular, bad) in enumerate(fine):
        rows.append(dict(spin=k+1, number_times_rs=number/(8*math.pi**2),
                         power_times_mass_squared=energy/(128*math.pi**3),
                         mean_x=energy/number, angular_nats_per_lost_entropy=angular/energy,
                         fraction_number_violating_in_lowest_wave=bad/number))
    n,e,ang,bad = sum(fine)
    return dict(particle_species=rows,
                combined_angular_nats_per_lost_entropy=ang/e,
                combined_fraction_number_excluded_in_lowest_wave=bad/n,
                largest_relative_quadrature_and_partial_wave_change=float(np.max(rel)),
                single_quantum=[one_energy(x) for x in (1.,2.,3.,5.,8.,12.,18.)])


def photon_pair_checks():
    # One photon in each of two disjoint spectral (or angular) ports. The
    # same-port two-boson scalar product is the permanent of its Gram matrix.
    def pairgram(u, v):
        polar = np.eye(2)
        def one_arm(signs, other, overlap):
            wave = np.array([[1.,overlap],[np.conj(overlap),1.]])
            matrix = np.array([[wave[i,j]*polar[signs[i],other[j]] for j in (0,1)] for i in (0,1)])
            return matrix[0,0]*matrix[1,1]+matrix[0,1]*matrix[1,0]
        words = [(0,0),(0,1),(1,0),(1,1)]
        return np.array([[one_arm(w,z,u)*one_arm(w,z,v) for z in words] for w in words])
    pairs = []
    for u,v in ((0.,0.),(0.4j,0.),(0.4j,0.8),(1.,1.)):
        matrix = pairgram(u,v)
        same = (1+abs(u)**2)*(1+abs(v)**2)
        opposite = 1+abs(u*v)**2
        even = np.array([[1,0,0,1],[0,1,1,0]]).T/math.sqrt(2)
        assert np.max(abs(even.T.conj()@matrix@even-np.diag([same,opposite])))<2e-15
        assert np.allclose(np.linalg.eigvalsh(matrix),sorted([same,same,opposite,2-opposite]))
        visibility = 2*math.sqrt(same*opposite)/(same+opposite)
        pairs.append(dict(overlap_amplitude_left=abs(u),overlap_amplitude_right=abs(v),
                          same_sign_norm=same, even_opposite_norm=opposite,
                          last_time_record_fidelity=(1+visibility)/2))
    return pairs


def four_photon_transfer():
    # Paired invariant masses x and y in units of total mass squared.
    def monomial(a, b):
        f = math.factorial
        return Fraction(f(a)*f(a+1)*f(b)*f(b+1), f(a+b+2)*f(a+b+3))

    normalization = monomial(2, 2)
    def moment(k):
        return sum(math.comb(k, j)*monomial(2+j, 2+k-j) for j in range(k+1))/normalization

    def product(poly, other):
        return sum(a*b*moment(i+j) for i,a in enumerate(poly) for j,b in enumerate(other))

    polys, norms = [], []
    for degree in range(6):
        poly = [Fraction(0)]*degree+[Fraction(1)]
        for previous, norm in zip(polys, norms):
            coeff = product(poly, previous)/norm
            for j,a in enumerate(previous):
                poly[j] -= coeff*a
        norm = product(poly, poly)
        assert norm > 0 and all(product(poly, p) == 0 for p in polys)
        polys.append(poly)
        norms.append(norm)

    mean = moment(1)
    variance = moment(2)-mean**2
    def cut_moment(k, upper):
        # Change coordinates independently to z=x+y and r=abs(x-y).
        def integral(z):
            lower = math.sqrt(max(0., 2*z-1))
            def integrand(t):
                r = lower+(z-lower)*t*t
                return ((z*z-r*r)**2*math.sqrt(max(0.,1-2*z+r*r))
                        *2*(z-lower)*t/16)
            return z**k*quad(integrand,0.,1.,epsabs=2e-14,epsrel=8e-11)[0]
        return sum(quad(integral,a,b,epsabs=8e-15,epsrel=8e-10)[0]
                   for a,b in zip([0.,min(.5,upper)],[min(.5,upper),upper]) if b>a)/float(normalization)

    errors = [abs(cut_moment(k,1.)-float(moment(k))) for k in range(5)]
    assert max(errors)<2e-8
    m, sd = float(mean), math.sqrt(float(variance))
    a,b,c = [cut_moment(k,m) for k in range(3)]
    effect = np.array([[a,(b-m*a)/sd],[(b-m*a)/sd,(c-2*m*b+m*m*a)/(sd*sd)]])
    eigenvalues = np.linalg.eigvalsh(effect)
    assert np.all((eigenvalues>0)&(eigenvalues<1))
    recover = sum(np.sum(np.sqrt(p))**2/4 for p in (eigenvalues, 1-eigenvalues))
    return dict(base_phase_space=str(normalization), mean_pair_mass_sum=str(mean),
                variance_pair_mass_sum=str(variance), monic_squared_norms=list(map(str,norms)),
                exact_orthogonal_modes=len(polys), independent_moment_error=max(errors),
                two_bin_effect_eigenvalues=eigenvalues.tolist(),
                two_bin_optimal_reference_fidelity=float(recover),
                full_shape_record_qubit_fidelity=.5)


def relative_plane_code():
    # Construct actual on-shell momenta with a common timelike total P from
    # two independently oriented pair decays. Signature is (+---).
    def metric(v,w):
        return v[0]*w[0]-np.dot(v[1:],w[1:])

    def boost(k,velocity):
        beta2 = np.dot(velocity,velocity)
        gamma = 1/math.sqrt(1-beta2)
        projection = np.dot(velocity,k[1:])
        return np.r_[gamma*(k[0]+projection),k[1:]+velocity*(gamma*k[0]+gamma**2*projection/(gamma+1))]

    def pair(energy,mass,cosine,angle,sign):
        transverse = math.sqrt(1-cosine*cosine)
        unit = np.array([transverse*math.cos(angle),transverse*math.sin(angle),cosine])
        velocity = np.array([0.,0.,sign*math.sqrt(1-(mass/energy)**2)])
        return [boost(mass/2*np.r_[1.,u*unit],velocity) for u in (1.,-1.)]

    def invariants(particles):
        p = np.sum(particles,axis=0)
        q = particles[0]+particles[1]
        a,b = particles[0]-particles[1],particles[2]-particles[3]
        p2, pq, q2 = metric(p,p),metric(p,q),metric(q,q)
        det = p2*q2-pq*pq
        adj = np.array([[q2,-pq],[-pq,p2]])
        def transverse(v,w):
            vv = np.array([metric(p,v),metric(q,v)])
            ww = np.array([metric(p,w),metric(q,w)])
            return det*metric(v,w)-vv@adj@ww
        return transverse(a,b), transverse(a,a)*transverse(b,b)

    def polynomials(n,ell,degree):
        # L^j T_(2j)(N/sqrt(L)) built by the double-angle recurrence.
        raw = [1., 2*n*n-ell]
        for j in range(2,degree+1):
            raw.append(2*raw[1]*raw[-1]-ell*ell*raw[-2])
        return np.array([(math.sqrt(2) if j else 1.)*ell**(degree-j)*raw[j]
                         for j in range(degree+1)])

    degree = 5
    gram_error = invariant_error = energy_error = 0.
    for x,y,u,v in ((.07,.12,-.45,.6),(.20,.08,.70,-.38),(.03,.08,-.91,.86)):
        samples = []
        initial = None
        for j in range(64):
            phi = 2*math.pi*(j+.23)/64
            photons = pair((1+x-y)/2,math.sqrt(x),u,0.,1)+pair((1-x+y)/2,math.sqrt(y),v,phi,-1)
            assert min(k[0] for k in photons)>0 and max(abs(metric(k,k)) for k in photons)<3e-15
            energy_error = max(energy_error,max(abs(np.sum(photons,axis=0)-np.array([1.,0.,0.,0.]))))
            energies = [k[0] for k in photons]
            if initial is None:
                initial = energies
            energy_error = max(energy_error,max(abs(np.array(energies)-initial)))
            n,ell = invariants(photons)
            amp = polynomials(n,ell,degree)/ell**degree
            samples.append(amp)
            reconstructed = np.array([1.]+[math.sqrt(2)*math.cos(2*h*phi) for h in range(1,degree+1)])
            invariant_error = max(invariant_error, max(abs(amp-reconstructed)))
            for alternate in (photons[2:]+photons[:2], [photons[1],photons[0],*photons[2:]],
                              [boost(k,np.array([.24,-.31,.18])) for k in photons]):
                n2,ell2 = invariants(alternate)
                invariant_error = max(invariant_error, max(abs(polynomials(n2,ell2,degree)/ell**degree-amp)))
        gram_error = max(gram_error, np.max(abs(np.array(samples).T@np.array(samples)/64-np.eye(degree+1))))
    assert max(energy_error,gram_error,invariant_error)<5e-10
    return dict(modes=degree+1, distinct_energy_shapes=3, finite_four_momentum_residual=energy_error,
                conditional_angular_gram_error=gram_error, boost_exchange_polynomial_error=invariant_error)


def helicity_transfer():
    # The scalar derivative vertex uses only P=sum k_i and V=sum(P.k_i) k_i.
    # Three-body and higher massless events in a rest frame. Each row is a
    # physical momentum and its two transverse unit polarization vectors.
    cases = []
    for seed in ([(.7,.1,.2),(-.2,.35,.6),(.14,-.55,.23)],
                 [(.51,.25,.31),(-.21,.49,-.26),(.34,-.23,.73)],
                 [(.31,.27,-.49),(-.72,.63,.11),(.44,.16,.57),(.37,-.25,.19),(-.15,.30,.47)]):
        spatial = np.array([*seed,-np.sum(seed,axis=0)])
        spatial /= sum(np.linalg.norm(v) for v in spatial)
        energy = np.linalg.norm(spatial,axis=1)
        rest_vector = np.sum(energy[:,None]*spatial,axis=0)
        amplitudes = []
        for e,k in zip(energy,spatial):
            ray = k/e
            t = np.cross(ray,[.29,.71,-.11])
            t /= np.linalg.norm(t)
            polar = (t+1j*np.cross(ray,t))/math.sqrt(2)
            z = e*np.dot(polar,rest_vector)
            amplitudes.append([z,z.conjugate()])
        count = len(spatial)
        words = list(product((0,1),repeat=count))
        sectors = [min(sum(h),count-sum(h)) for h in words]
        degeneracy = np.bincount(sectors)
        raw = np.array([np.prod([amplitudes[i][s] for i,s in enumerate(h)]) for h in words])
        base = abs(raw[0])
        assert base>0
        encoder = np.array([[u/base/math.sqrt(degeneracy[j]) if sector==j else 0
                            for j in range(len(degeneracy))] for u,sector in zip(raw,sectors)])
        gram = encoder.conj().T@encoder
        single = encoder[[w[0]==0 for w in words]]
        same = encoder[[w[0]==w[1] for w in words]]
        matched = np.real(np.diag(same.conj().T@same))
        expected = [1-2*j*(count-j)/(count*(count-1)) for j in range(len(degeneracy))]
        assert np.allclose(gram, np.eye(len(degeneracy))) and np.allclose(single.conj().T@single,gram/2)
        assert np.allclose(matched,expected)
        p = np.array(expected)
        fidelity = (np.sum(np.sqrt(p))**2+np.sum(np.sqrt(1-p))**2)/len(p)**2
        cases.append(dict(photons=count, logical_states=len(degeneracy), helicity_counts=degeneracy.tolist(),
                          fixed_momentum_gram_error=float(np.max(abs(gram-np.eye(len(p))))),
                          one_helicity_gram_error=float(np.max(abs(single.conj().T@single-np.eye(len(p))/2))),
                          two_helicity_equal_probabilities=expected, relative_helicity_fidelity=float(fidelity)))
    # The trace-free transverse energy quadrupole of the relative-plane code
    # fixes cos(2 phi) with the kinematic coefficients A and B recorded.
    errors=[]
    for phi in (.15,1.01,2.2):
        a,b=.73,.24
        d=a+b*np.exp(2j*phi)
        errors.append(abs((abs(d)**2-a*a-b*b)/(2*a*b)-math.cos(2*phi)))
    return dict(packets=cases, plane_from_quadrupole_error=max(errors))


def one_soft_graviton_code():
    # The 12 hard momenta distinguish legs. Bit flips and phases span all
    # one-leg linear spin errors, including their coherent linear combinations.
    count=12
    indices=np.arange(2**count,dtype=int)
    weights=np.array([int(i).bit_count() for i in indices])
    logical=np.zeros((len(indices),2),complex)
    for k,coef,column in ((0,1/math.sqrt(8),0),(6,math.sqrt(6/8),0),
                          (12,1/math.sqrt(8),0),(3,1/math.sqrt(2),1),(9,1/math.sqrt(2),1)):
        logical[weights==k,column]=coef/math.sqrt(math.comb(count,k))
    errors=[logical]
    for leg in range(count):
        mask=1<<leg
        sign=1-2*((indices>>leg)&1)
        errors.extend([logical[indices^mask], sign[:,None]*logical,
                       (-1j*sign)[:,None]*logical[indices^mask]])
    operators=np.stack(errors,axis=1)
    a,b=operators[:,:,0],operators[:,:,1]
    # Pairwise Knill--Laflamme conditions also cover arbitrary unresolved
    # superpositions of errors and any external reference.
    mismatch=float(np.max(abs(a.conj().T@a-b.conj().T@b)))
    cross=float(np.max(abs(a.conj().T@b)))
    # Test the product rule for a momentum-dependent local choice of
    # helicity phase. The derivative on any leg may depend on all momenta.
    signs=np.stack([1-2*((indices>>i)&1) for i in range(count)],axis=1)
    coeff=np.sin(np.arange(1,count+1)*.63)/count
    phase=signs@coeff
    t=.41
    dressed=lambda u: np.exp(1j*u*phase)[:,None]*logical
    diff=(dressed(t+1e-5)-dressed(t-1e-5))/(2e-5)
    product_error=float(np.max(abs(diff-1j*phase[:,None]*dressed(t))))
    assert max(mismatch,cross,product_error)<3e-10
    # Directly differentiate the tensor vertex along the orbital + spin
    # Lorentz generators in the stripped tree-level soft-graviton factor.
    coordinates=np.arange(1,count)
    ks=np.stack([np.sin(.93*coordinates),np.cos(.71*coordinates),
                 np.sin(.37*coordinates+.48)],axis=1)
    ks=np.vstack([ks,-ks.sum(axis=0)])
    energies=np.linalg.norm(ks,axis=1)
    ks=np.column_stack([energies,ks])/energies.sum()
    dirs=ks[:,1:]/ks[:,0,None]
    e1=np.cross(dirs,[.31,-.61,.73])
    e1/=np.linalg.norm(e1,axis=1)[:,None]
    polar=np.column_stack([np.zeros(count),(e1+1j*np.cross(dirs,e1))/math.sqrt(2)])
    metric=np.diag([1.,-1.,-1.,-1.])
    def vertex(k,pol):
        total=k.sum(axis=0)
        kp=k@metric@total
        vector=kp@k
        return kp*(pol@metric@vector)-(pol@metric@total)*(k@metric@vector)
    base=vertex(ks,polar)
    assert min(abs(base))>0
    def encoded(u):
        relative=u/abs(base)
        leg_values=np.where(signs==1,relative,relative.conjugate())
        return np.prod(leg_values,axis=1)[:,None]*logical
    soft_maps=[encoded(base)]
    hard_charge_error=0.
    wave=np.array([1.,0.,0.,1.])
    for spatial_tensor in (np.diag([1.,-1.,0.]), np.array([[0.,1.,0.],[1.,0.,0.],[0.,0.,0.]])):
        generators=[]
        for k in ks:
            tt=np.r_[0.,spatial_tensor@k[1:]]
            generators.append((np.outer(wave,tt@metric)-np.outer(tt,wave@metric))/(k@metric@wave))
        step=1e-6
        vertices=[]
        for eps in (step,-step):
            mats=np.array([expm(eps*B) for B in generators])
            k=np.einsum("ijk,ik->ij",mats,ks)
            pol=np.einsum("ijk,ik->ij",mats,polar)
            hard_charge_error=max(hard_charge_error,float(np.max(abs(np.sum((k@metric)*k,axis=1)))),
                                  float(np.max(abs(np.sum((pol@metric)*k,axis=1)))))
            vertices.append(encoded(vertex(k,pol)))
        soft_maps.append((vertices[0]-vertices[1])/(2*step))
    gram_residual=0.
    for left in soft_maps:
        for right in soft_maps:
            eff=left.conj().T@right
            gram_residual=max(gram_residual,float(np.max(abs(eff-np.eye(2)*np.trace(eff)/2))
                                                  /max(1.,np.linalg.norm(left)*np.linalg.norm(right))))
    assert gram_residual<2e-8 and hard_charge_error<1e-14
    return dict(hard_photons=count, single_leg_basis_errors=len(errors),
                explicit_soft_tree_gram_residual=gram_residual,
                mass_shell_and_transverse_error=hard_charge_error,
                tested_error_products=len(errors)**2, scalar_gram_difference=mismatch,
                off_diagonal_gram=cross, product_derivative_error=product_error,
                two_leg_symmetric_density=["13/44","9/22","13/44"])


def pair_spectrum_check():
    # Positive Laplace reconstruction. Use an independently integrable dipole
    # window x^4 for this identity test. The physical greybody is tested above.
    def density(a):
        n = math.floor(a)
        return (n*a*a-a*n*(n+1)+n*(n+1)*(2*n+1)/6)/2
    def laplace(x):
        return sum(quad(lambda a: density(a)*math.exp(-a*x), n,n+1,
                        epsabs=3e-14)[0] for n in range(1,1+math.ceil(60/x)))
    # For w=x^7, L_w(a)=7!/a^8. Multiplication by L_w in the untagged-leg
    # integral cancels its reciprocal exactly. Integer-a endpoint jumps in the
    # second derivative are explicitly included in the quadrature above.
    errors = [abs(laplace(x)*x**3*math.expm1(x)-1) for x in (.4,1.,3.,8.)]
    assert max(errors)<2e-12
    # The smooth + terminal example after n ordinary emissions with M_n=2^-n.
    # Tail beyond N is bounded by sum of odds, N chosen to dominate roundoff.
    log_survival = -sum(math.log1p(2.**(-4*n)) for n in range(28))
    return dict(laplace_relative_error=max(errors), continuous_mass_chain_survival=math.exp(log_survival),
                last_omitted_sum_bound=2.**(-112)/(1-2.**-4))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
                        default=ROOT/"verification"/"tidal-hawking-multiplicities-results.json")
    output = parser.parse_args().output
    result = dict(tidal=tidal_check(), receiver=finite_mass_receiver(), causal_line=causal_line_receiver(), hawking=greybody(), pair_transfer=photon_pair_checks(),
                  four_photon=four_photon_transfer(), relative_plane=relative_plane_code(), helicity=helicity_transfer(), one_soft=one_soft_graviton_code(),
                  pair_spectrum=pair_spectrum_check())
    output.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    print(output.name)
