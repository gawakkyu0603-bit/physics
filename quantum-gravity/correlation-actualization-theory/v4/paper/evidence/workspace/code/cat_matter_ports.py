"""Material index birth, the Ricci breathing mode and causal delivery in CAT.

The BFSS calculation uses dimensionless matrix variables. The dust calculation
specifies a material clock and reports times for a ten-solar-mass cloud. No
ensemble probability is identified with the probability of a gravitational write.
"""
import argparse
import json
from math import acos, ceil, cos, pi, sqrt
from pathlib import Path

import numpy as np
from scipy import constants, linalg
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq


ROOT = Path(__file__).resolve().parents[1]
SIGMA = (np.array([[0., 1.], [1., 0.]]),
         np.array([[0., -1j], [1j, 0.]]), np.diag([1., -1.]))
I2 = np.eye(2)
HORIZON_TIME = 4*10*1.3271244e20/(3*constants.c**3)


def op(axes, point):
    return sum(np.kron(p, a*p-y*I2) for p,a,y in zip(SIGMA,axes,point))


def half_signature(axes,point):
    spectrum = linalg.eigvalsh(op(axes,point))
    assert min(abs(spectrum)) > 1.e-10
    return int(sum(np.sign(spectrum))/2)


def principal_readout(axes):
    # Largest axis is z in the Bell-block convention.
    a,b,c = sorted(axes,reverse=True)
    r = sqrt(max(a*a-b*b,0.))
    numerical = linalg.eigvalsh(op([b,c,a],[0.,0.,r]))
    diagonal = sorted([a-sqrt(r*r+(b-c)**2),a+sqrt(r*r+(b-c)**2),
                       -a-sqrt(r*r+(b+c)**2),-a+sqrt(r*r+(b+c)**2)])
    np.testing.assert_allclose(numerical,diagonal,atol=1e-13)
    assert sum(np.sign(numerical)) == 2
    min_gap=float(min(abs(numerical)))
    assert min_gap >= b*c/(2*a)-2e-15
    purity=sum(s**4 for s in axes)/sum(s*s for s in axes)**2
    centred=half_signature([b,c,a],[0.,0.,0.])
    assert (centred==1)==(purity<.5)
    return dict(axes=axes,centre_index=centred,gram_purity=purity,
                focus=r,focus_gap=min_gap,certified_ball=b*c/(2*a))


def centre_chance(dim):
    # Integrate the real-Wishart singular-value density after scaling away s1.
    def inner(u,inside):
        low=max(1-u,0.) if inside else 0.
        def integrand(v):
            numerator=(u*v)**(dim-3)*(1-u*u)*(1-v*v)*(u*u-v*v)
            return numerator/(1+u*u+v*v)**(3*dim/2)
        return quad(integrand,low,u,epsabs=1e-31,epsrel=3e-11)[0]
    integrals=[quad(lambda u:inner(u,inside),.5 if inside else 0.,1.,
                    epsabs=1e-30,epsrel=3e-11)[0] for inside in (False,True)]
    return integrals[1]/integrals[0]


def thermal_shapes():
    rng=np.random.default_rng(146)
    rows=[]
    for dim in (3,4,6,9):
        probability=centre_chance(dim)
        count=0
        samples=65536
        for _ in range(samples//1024):
            v=rng.normal(size=(1024,dim,3))
            gram=v.transpose(0,2,1)@v
            purities=np.sum(gram**2,axis=(1,2))/np.trace(gram,axis1=1,axis2=2)**2
            count+=int(np.count_nonzero(purities<.5))
        fraction=count/samples
        sampling_sigma=sqrt(probability*(1-probability)/samples)
        assert abs(fraction-probability)<5*sampling_sigma
        rows.append(dict(velocity_dimensions=dim,quadrature=probability,
                         monte_carlo=fraction,samples=samples))
    return rows


def wall_arrival():
    # Choose the horizon proper-time scale as unit, and rescale the matrices
    # by the inverse BFSS clock unit. The sphere starts as a point.
    end=.2
    emission_u=1.2**3
    birth_u=emission_u+end
    speeds=np.array([1.2,.6,3.])
    def curvature(t):
        return 2/(9*(birth_u-t)**2)
    def motion(t,y):
        axes,vel=y[:3],y[3:]
        return np.r_[vel,-curvature(t)*axes-4*axes*(np.dot(axes,axes)-axes**2)]
    sol=solve_ivp(motion,(0.,.32),np.r_[np.zeros(3),speeds],dense_output=True,
                  rtol=1e-12,atol=2e-14,method="DOP853")
    final=sol.sol(end)[:3]
    kmax=curvature(end)
    epsilon=kmax*end**2/6+np.dot(speeds,speeds)*end**4/5
    bound=end*np.sum(speeds)*epsilon
    assert np.sum(abs(final-end*speeds)) <= bound
    focus=end*sqrt(speeds[2]**2-speeds[0]**2)
    point=np.array([0.,0.,focus])
    start_index=half_signature([0.]*3,point)
    end_index=half_signature(final,point)
    assert (start_index,end_index)==(0,1)
    def determinant(t):
        return float(linalg.det(op(sol.sol(t)[:3],point)).real)
    crossing=brentq(determinant,0.,end)
    departure=brentq(determinant,end,.32)
    np.testing.assert_array_equal([half_signature(sol.sol(t)[:3],point) for t in (.18,.20,.30)],[0,1,0])
    mesh=.01
    inradius=end*speeds[0]*speeds[1]/(2*speeds[2])
    assert bound+mesh<inradius
    # Check the same evolution in a nine-matrix non-principal basis directly.
    rng=np.random.default_rng(92)
    rotation,_=linalg.qr(rng.normal(size=(9,3)),mode='economic')
    initial_vel=np.stack([sum(row[j]*speeds[j]*SIGMA[j] for j in range(3))
                          for row in rotation])
    mask=rotation@rotation.T
    def full(t,y):
        y=y.reshape(2,9,2,2)
        x,v=y
        comm=x[:,None]@x[None,:]-x[None,:]@x[:,None]
        double=np.sum(x[:,None]@comm-comm@x[:,None],axis=0)
        # The isotropic dust tide acts in the physical material three-plane.
        return np.stack([v,-double-curvature(t)*np.einsum('ij,jab->iab',mask,x)]).ravel()
    state=np.stack([np.zeros_like(initial_vel),initial_vel]).ravel()
    full_end=solve_ivp(full,(0.,end),state,method="DOP853",rtol=2e-12,atol=2e-14).y[:,-1].reshape(2,9,2,2)
    x,v=full_end
    expected=np.stack([sum(row[j]*final[j]*SIGMA[j] for j in range(3)) for row in rotation])
    np.testing.assert_allclose(x,expected,atol=1e-12)
    np.testing.assert_allclose(sum(x@v-v@x),0,atol=4e-13)
    return dict(velocities=speeds.tolist(),deadline=end,actual_axes=final.tolist(),
                focal_port_radius=focus,index_at_birth=start_index,index_at_deadline=end_index,
                entry=crossing,exit=departure,live_window=departure-crossing,
                birth_remaining_time=birth_u,linearisation_error_bound=bound,
                linearisation_error=float(sum(abs(final-end*speeds))),
                minimum_gap_for_linear_pencil=inradius,mesh_covering_radius=mesh,
                margin_after_mesh_and_error=inradius-mesh-bound)


def ricci_transfer(k):
    s=sqrt(k)
    def basis(z):
        return np.array([[z*z,z],[-2/(3*z),-1/(3*z*z)]])
    start=s**3
    S=basis(1.)@linalg.inv(basis(s))
    S0=np.array([[1.,start-1],[0.,1.]])
    relative=S@linalg.inv(S0)
    trace=2-(s+1/s-2)**2/3
    np.testing.assert_allclose(np.trace(relative),trace,atol=1e-13)
    def ode(u,state):
        x,v=state.reshape(2,2)
        return np.r_[-v,2*x/(9*u*u)]
    observed=solve_ivp(ode,(start,1.),np.eye(2).ravel(),method='DOP853',
                       rtol=3e-12,atol=3e-14).y[:,-1].reshape(2,2)
    np.testing.assert_allclose(S,observed,rtol=4e-10,atol=1e-11)
    eig,rows=linalg.eig(relative.T)
    sel=np.argmin(eig.real)
    assert abs(eig[sel].imag)<1e-12 and eig[sel].real<0
    row=rows[:,sel].real
    np.testing.assert_allclose(row@S,eig[sel].real*(row@S0),atol=2e-12)
    if (row@S0)[0]<0:
        row=-row
    incoming=row@S0
    comoving=incoming[0]-2*incoming[1]/(3*start)
    tag_u=HORIZON_TIME*(1.2**3+.2)
    material=[]
    for mass,separation in ((1.31e-9,1.e-4),(70.,1.)):
        quantum_width=sqrt(abs(incoming[0]*incoming[1])*tag_u*constants.hbar/mass)
        speed5=abs(comoving)*separation/(5*abs(incoming[1])*tag_u)
        material.append(dict(effective_mass_kg=mass,initial_separation_m=separation,
                             quantum_limited_signal_over_width=abs(comoving)*separation/quantum_width,
                             rms_speed_for_five_sigma_ms=speed5))
    return dict(radii_ratio=k,relative_trace=float(trace),negative_scale=float(eig[sel].real),
                readout_row=row.tolist(),incoming_row=incoming.tolist(),comoving_coefficient=comoving,
                macroscopic_pairs=material)


def certify_pulse():
    """Rational Taylor residual and exact brackets for the two charge edges."""
    from fractions import Fraction as F
    order=24
    U=F(241,125)
    stop=F(6,25)
    speeds=[F(6,5),F(3,5),F(3)]
    def poly_sum(p,q):
        size=max(len(p),len(q))
        return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(size)]
    def product(p,q):
        out=[F(0)]*(len(p)+len(q)-1)
        for i,a in enumerate(p):
            for j,b in enumerate(q):
                out[i+j]+=a*b
        return out
    def evaluate(p,x):
        value=F(0)
        for coefficient in reversed(p):
            value=value*x+coefficient
        return value
    kappa=[2*(n+1)/(9*U**(n+2)) for n in range(order)]
    approx=[[F(0),v] for v in speeds]
    for n in range(order-1):
        squared=[product(p,p) for p in approx]
        updates=[]
        for i,p in enumerate(approx):
            others=poly_sum(squared[(i+1)%3],squared[(i+2)%3])
            nonlinear=sum(p[k]*others[n-k] for k in range(n+1))
            tide=sum(p[k]*kappa[n-k] for k in range(n+1))
            updates.append(-(4*nonlinear+tide)/((n+1)*(n+2)))
        for p,x in zip(approx,updates):
            p.append(x)
    squared=[product(p,p) for p in approx]
    residual=F(0)
    for i,p in enumerate(approx):
        assert evaluate(list(map(abs,p)),stop)<1
        second=[(k+1)*(k+2)*v for k,v in enumerate(p[2:])]
        others=poly_sum(squared[(i+1)%3],squared[(i+2)%3])
        poly=poly_sum(second,[4*v for v in product(p,others)])
        cleared=poly_sum(product([U**2,-2*U,1],poly),[F(2,9)*v for v in p])
        residual=max(residual,evaluate(list(map(abs,cleared)),stop)/(U-stop)**2)
    error=residual*stop**2/(2-25*stop**2)
    assert 2>25*stop**2 and error<F(1,10**12)
    # All three true axes stay positive. The integral speed bounds imply
    # increasing squared outer and inner radii, so no edge is missed.
    km=F(2,9)/(U-stop)**2
    vv=sum(x*x for x in speeds)
    e=km*stop**2/6+vv*stop**4/5
    de=km*stop**2/2+vv*stop**4
    assert (1-e)*(1-de)*speeds[2]**2>(speeds[0]+speeds[1])**2 and de<1
    rr=F(1,25)*(speeds[2]**2-speeds[0]**2)
    def boundary(t,sign):
        b,c,a=(evaluate(p,t) for p in approx)
        return a*a-(b+sign*c)**2-rr
    starts=[F('0.18722545'),F('0.18722548')]
    ends=[F('0.22893286'),F('0.22893290')]
    for interval,edge in ((starts,-1),(ends,1)):
        assert boundary(interval[0],edge)<-10*error and boundary(interval[1],edge)>10*error
    son=[F('1.20294980'),F('1.20294983')]
    soff=[F('1.19326483'),F('1.19326486')]
    for s,interval in ((son,starts),(soff,ends)):
        assert s[0]**3 < U-interval[1] <= U-interval[0] < s[1]**3
    uh=F(4*10*132712440000000000000,3*299792458**3)
    wait=F(1,2000000)/uh
    w=[F('1.00253139'),F('1.00253142')]
    assert w[0]**3<1+wait<w[1]**3
    dlo=[2*(t-1) for t in soff]
    dhi=[2*(son[0]-w[1]),2*(son[1]-w[0])]
    y=F(4,5)
    min_area=(dhi[0]**2-dlo[1]**2)/(4*y)
    max_area=(dhi[1]**2-dlo[0]**2)/(4*y)
    assert F(1,285)<min_area<=max_area<F(1,284)
    assert y*F(22,7)/352<(dhi[0]-dlo[1])/2
    mid_lower=(dhi[0]+dlo[0])/2
    assert (1+y*y-mid_lower**2)/(2*y) < 1-(F(22,7)/10)**2/2
    return dict(polynomial_degree=order,uniform_axis_error_upper=float(error),
                entry_bracket=list(map(float,starts)),exit_bracket=list(map(float,ends)),
                half_microsecond_area_bounds=[float(min_area),float(max_area)],
                necessary_by_area=285,sufficient_meridian_sites=1760)


def shell_force():
    # Direct integration of the radial acceleration around a shell of unit
    # radius, for a source at distance d and with G*M=1.
    rows=[]
    for d in (0.,.25,.83,1.08,1.6,3.):
        integrand=lambda z: -(1-d*z)/(1+d*d-2*d*z)**1.5/2
        response=quad(integrand,-1,1,epsabs=5e-13)[0]
        analytic=-1. if d<1 else 0.
        np.testing.assert_allclose(response,analytic,atol=3e-14)
        rows.append(dict(source_distance_over_radius=d,mean_radial_force=response))
    return rows


def dust_delivery(wall):
    s_emit=1.2
    y=.8
    distance=2*(s_emit-1)
    mu=(1+y*y-distance*distance)/(2*y)
    fraction=(1-mu)/2
    worst_dot=2*cos(pi/12)-1
    chord=sqrt(1+y*y-2*y*worst_dot)
    arrival=s_emit-chord/2
    assert arrival>1 and worst_dot>mu
    emitters=[[0.,0.,1.],[0.,0.,-1.]]
    for j in range(1,6):
        th=j*pi/6
        for l in range(12):
            ph=l*pi/6
            emitters.append([np.sin(th)*cos(ph),np.sin(th)*np.sin(ph),cos(th)])
    n=np.asarray(emitters)
    i=np.arange(12000)+.5
    z=1-2*i/len(i)
    phase=pi*(3-sqrt(5))*i
    directions=np.column_stack([np.sqrt(1-z*z)*np.cos(phase),np.sqrt(1-z*z)*np.sin(phase),z])
    min_dot=float(np.min(np.max(directions@n.T,axis=1)))
    assert min_dot>=worst_dot
    son=(wall["birth_remaining_time"]-wall["entry"])**(1/3)
    soff=(wall["birth_remaining_time"]-wall["exit"])**(1/3)
    annuli=[]
    for response_us in (0.,.5,1.):
        lo=max(1-y,2*(soff-1))
        hi=min(1+y,2*(son-(1+response_us*1e-6/HORIZON_TIME)**(1/3)))
        assert hi>lo
        area=(hi**2-lo**2)/(4*y)
        # Spacing on each selected source meridian leaves an angular error
        # of at most pi/bands relative to an ideal point on that meridian.
        bands=int(np.floor(2*pi*y/(hi-lo)))+1
        net=y*pi/bands
        assert net<(hi-lo)/2
        mid=(hi+lo)/2
        theta=acos((1+y*y-mid*mid)/(2*y))
        meridians=ceil(pi/(2*theta))
        # Some meridian comes closer than theta to each destination and
        # hence intersects its entire circle of ideal emission directions.
        # The closest actual emitter on it differs by at most pi/bands.
        total_sources=meridians*bands
        assert pi/(2*meridians)<=theta
        # Verify a subset of target points against actual source positions,
        # independently of the all-directions angular covering bound.
        lat=2*pi*np.arange(bands)/bands
        ring_sources=np.concatenate([np.column_stack([
            np.sin(lat)*cos(j*pi/meridians),np.sin(lat)*np.sin(j*pi/meridians),np.cos(lat)])
            for j in range(meridians)])
        for dest in directions[::59]:
            lengths=np.sqrt(np.maximum(0.,1+y*y-2*y*(ring_sources@dest)))
            assert np.any((lo<lengths)&(lengths<hi))
        top=son-mid/2
        bottom=soff-mid/2
        dwell=HORIZON_TIME*(top**3-1)*1e6
        assert bottom<1 and dwell>response_us
        annuli.append(dict(required_response_us=response_us,min_chord=lo,max_chord=hi,
                          area_fraction=area,minimum_source_count=ceil(1/area),
                          samples_per_meridian=bands,meridian_count=meridians,sufficient_source_count=total_sources,
                          net_chord_error=net,central_annulus_dwell_us=dwell))
    threshold=((2+2*sqrt(3)+sqrt((2+2*sqrt(3))**2-4))/2)**2
    return dict(horizon_time_s=HORIZON_TIME,event_emission_s=s_emit,
                current_charge_annuli=annuli,emission_s_on=son,emission_s_off=soff,
                maximum_horizon_response_us=HORIZON_TIME*((1+son-soff)**3-1)*1e6,comoving_source_fraction=y,
                emission_radius_over_rs=s_emit**2,earliest_arrival_radius_over_rs=(s_emit-(1-y)/2)**2,
                area_fraction=fraction,necessary_count=ceil(1/fraction-1e-11),sufficient_grid_count=len(n),
                angular_radius_degrees=acos(mu)*180/pi,latest_proven_arrival_s=arrival,
                surface_minimum_time_left_us=1e6*HORIZON_TIME*(arrival**3-1),
                direct_meridian_time_left_us=1e6*HORIZON_TIME*((s_emit-(1-y)/2)**3-1),
                numerical_worst_nearest_dot=min_dot,analytic_lower_dot=worst_dot,
                k_threshold=threshold,central_release_threshold_over_rs=2.25*threshold,
                inward_horizon_comoving_fraction=3-2*s_emit,
                launch_to_tag_ms=1e3*HORIZON_TIME*215*(s_emit**3+.2))


def unresolved_rotor_energy():
    """Vibrational energy exchange with every magnetic final state retained."""
    identity = np.eye(3)
    axis = identity[2]
    derivative = np.zeros((3, 3, 3, 3))
    for i, j, k, l in np.ndindex(3, 3, 3, 3):
        single_trace = (identity[i,j]*axis[k]*axis[l] + identity[i,k]*axis[j]*axis[l]
                        + identity[i,l]*axis[j]*axis[k] + identity[j,k]*axis[i]*axis[l]
                        + identity[j,l]*axis[i]*axis[k] + identity[k,l]*axis[i]*axis[j])
        double_trace = (identity[i,j]*identity[k,l] + identity[i,k]*identity[j,l]
                        + identity[i,l]*identity[j,k])
        derivative[i,j,k,l] = 105*axis[i]*axis[j]*axis[k]*axis[l] - 15*single_trace + 3*double_trace

    # Independently integrate the angular quadrupole in the real p_x,p_y,p_z basis.
    quadrupole = np.zeros((3, 3, 3, 3))
    nodes, weights = np.polynomial.legendre.leggauss(6)
    for cosine, weight in zip(nodes, weights):
        for azimuth in 2*pi*np.arange(12)/12:
            unit = np.array([sqrt(1-cosine**2)*cos(azimuth),
                             sqrt(1-cosine**2)*np.sin(azimuth), cosine])
            projector = np.outer(unit, unit)
            quadrupole += (3*weight/24)*np.einsum('ab,ij->ijab', projector, projector-identity/3)
    exchange = 25*np.einsum('ijkl,ijab,klcd->acbd', derivative, quadrupole, quadrupole)/24
    coupling = exchange.reshape(9, 9)
    np.testing.assert_allclose(exchange, derivative.transpose(0,2,1,3)/6, atol=5e-14)
    np.testing.assert_allclose(linalg.eigvalsh(coupling), [-4,-4,0,0,0,0,1,1,6], atol=1e-13)
    plus = np.array([1., 1j, 0.])/sqrt(2)
    minus = plus.conj()
    along = np.kron(plus, plus)
    opposite = np.kron(minus, plus)
    odd = (opposite - np.kron(plus, minus))/sqrt(2)
    np.testing.assert_allclose(coupling@odd, 0., atol=1e-14)
    np.testing.assert_allclose(coupling@along, along, atol=1e-14)
    np.testing.assert_allclose([np.linalg.norm(coupling@v)**2 for v in (along,opposite)], [1.,6.], atol=1e-13)

    def probability(hamiltonian, state, time):
        incoming = np.r_[state, np.zeros(9)]
        transferred = (linalg.expm(-1j*hamiltonian*time)@incoming)[9:]
        return np.linalg.norm(transferred)**2

    zeros = np.zeros_like(coupling)
    balanced = np.block([[zeros, coupling], [coupling, zeros]])
    f = lambda x: np.sin(x)**2 - np.sin(6*x)**2/6
    crossing = brentq(f, .1, pi/6)
    rows = []
    for x in (.1, crossing, pi/6, pi/2):
        parallel = probability(balanced, along, x)
        antiparallel = probability(balanced, opposite, x)
        np.testing.assert_allclose([parallel,antiparallel], [np.sin(x)**2,np.sin(6*x)**2/6], atol=1e-14)
        rows.append(dict(pulse_area=x,parallel=parallel,antiparallel=antiparallel))

    # Axially symmetric ordinary static shifts. Interchanging the identical
    # molecules interchanges the two diagonal blocks, leaving equal energies
    # in the one-dimensional parallel sector and preserving the odd dark mode.
    axial_shift = np.diag([1., 1., -2.])
    left = np.kron(axial_shift, identity)
    right = np.kron(identity, axial_shift)
    detuned = []
    for splitting, diagonal_force in ((.7,.13), (9.,2.), (30.,-.8)):
        initial_block = splitting*(1.4*left+right)+diagonal_force*coupling
        final_block = splitting*(left+1.4*right)+diagonal_force*coupling
        full = np.block([[initial_block, coupling],[coupling, final_block]])
        p_at_half = probability(full, opposite, pi/2)
        np.testing.assert_allclose(probability(full, along, pi/2), 1., atol=1e-13)
        assert p_at_half <= .5+1e-13
        arc = [probability(full, opposite, t) for t in np.linspace(0., pi/2, 17)]
        assert max(arc) <= .5+1e-13
        detuned.append(dict(axial_shift=splitting,diagonal_quadrupole=diagonal_force,
                            opposite_at_parallel_maximum=p_at_half))
    return dict(exchange_spectrum=[-4,-4,0,0,0,0,1,1,6],
                weak_coefficients=[1.,6.],first_balanced_crossing=crossing,
                balanced_examples=rows,static_shift_examples=detuned)


def angular_records():
    """Compare the charge alone with a joint receipt of charge and receiver axis."""
    raising = sqrt(2) * np.diag([1., 1.], 1)
    generators = ((raising + raising.T) / 2, (raising - raising.T) / (2j),
                  np.diag([1., 0., -1.]))

    def bright_projector(axis):
        component = sum(n * spin for n, spin in zip(axis, generators))
        return (component @ component + component) / 2

    # The prepared spin-one source has m_z = +1 or -1 with equal prior.
    # A unit-bright transition is shown; at finite interaction time all
    # contrasts below are multiplied by sin^2 of the physical pulse area.
    directions = np.concatenate((np.eye(3), -np.eye(3)))
    effects = np.array([bright_projector(axis) for axis in directions])
    np.testing.assert_allclose(effects.mean(axis=0), np.eye(3) / 3, atol=1e-15)
    finite_biases = (effects[:, 0, 0] - effects[:, 2, 2]).real
    np.testing.assert_allclose(finite_biases, directions[:, 2], atol=1e-15)
    finite_tagged = np.mean(np.abs(finite_biases))

    def click_difference(cosine):
        axis = (sqrt(max(0., 1.-cosine**2)), 0., cosine)
        effect = bright_projector(axis)
        observed = np.diag(effect).real[[0, 2]]
        expected = ((1.+cosine)**2 / 4, (1.-cosine)**2 / 4)
        np.testing.assert_allclose(observed, expected, atol=1e-15)
        return float(observed[0] - observed[1])

    untagged = abs(quad(click_difference, -1, 1)[0]) / 2
    tagged = quad(lambda c: abs(click_difference(c)), -1, 1, points=[0])[0] / 2
    np.testing.assert_allclose([untagged, tagged, finite_tagged], [0., .5, 1./3], atol=1e-15)
    return dict(aligned_charge_distance=1., isotropic_charge_distance=untagged,
                isotropic_joint_distance=tagged, six_axes_joint_distance=finite_tagged,
                isotropic_joint_success_equal_priors=(1.+tagged)/2)


def inclusive_recovery():
    # The environmental tag is independent of the quantum payload. After
    # routing, use a coherent emission into species plus core of total dim 12.
    rng=np.random.default_rng(1461)
    raw=rng.normal(size=(12,4))+1j*rng.normal(size=(12,4))
    emission,_=linalg.qr(raw,mode='economic')
    np.testing.assert_allclose(emission.conj().T@emission,np.eye(4),atol=1e-14)
    record=np.array([.5,.5])   # equal incident weights on two reflection-related receiving ports
    # Both histories deposit a unit; they use different identified physical
    # receivers. Each routes to the surface at the same preterminal cut.
    channels=[sqrt(p)*emission for p in record]
    for p,K in zip(record,channels):
        np.testing.assert_allclose(K.conj().T@K,p*np.eye(4),atol=1e-14)
    # Couple an unwanted quadrupolar excitation into the monopole readout.
    # Keep every species and the core. Only the deposited charge has been read.
    angles=[]
    for strength in (0.,.1,.3):
        p0=np.sin(.6+strength)**2
        p1=np.sin(.6-strength)**2
        diag=np.array([p0,p1,p0,p1])
        amplitude=[emission@np.diag(np.sqrt(row)) for row in (diag,1-diag)]
        fidelity=sum(sum(linalg.svdvals(K))**2 for K in amplitude)/16
        exact=(1+sqrt(p0*p1)+sqrt((1-p0)*(1-p1)))/2
        np.testing.assert_allclose(fidelity,exact,atol=2e-15)
        angles.append(dict(mixing_angle=strength,charge_distance=abs(p0-p1),all_output_fidelity=float(fidelity)))
    return dict(illustrative_independent_weights=record.tolist(),examples_with_mixing=angles)


def draw_figure(report,path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle
    data=report["surface"]
    y=data["comoving_source_fraction"]
    # A meridional section: the ordinary unknown payload lies outside a
    # small permeable breathing shell. The solid arrow is the material signal.
    fig,(left,right)=plt.subplots(1,2,figsize=(8.4,3.15),layout="constrained")
    left.set_aspect("equal")
    left.add_patch(Circle((0,0),1,ec="#343f49",fc="#ecf3f3",lw=1.25))
    left.add_patch(Circle((.62,.05),.19,ec="#235e77",fc="white",lw=1.6))
    pts=np.array([[.62,.05],[.55,.10],[.70,.10],[.62,-.03],[.54,.00]])
    left.scatter(*pts.T,s=7,color="#235e77")
    left.scatter([-.3],[.2],color="#a44723",s=35)
    left.annotate("A",(-.3,.2),(-.48,.32))
    left.annotate("outgoing signal",xy=(.95,.23),xytext=(.05,.67),
                  arrowprops={"arrowstyle":"->","color":"#235e77"},fontsize=9)
    left.text(0,-.55,"dust",ha="center")
    left.text(.57,-.28,"breathing shell",ha="center",fontsize=9)
    left.set(xlim=(-1.07,1.1),ylim=(-1.05,1.05))
    left.axis("off")
    theta=np.linspace(14,29,240)
    chord=np.sqrt(1+y*y-2*y*np.cos(np.deg2rad(theta)))
    def lead(s): return 1.e6*HORIZON_TIME*((s-chord/2)**3-1)
    enter=lead(data["emission_s_on"])
    leave=lead(data["emission_s_off"])
    right.fill_between(theta,leave,enter,color="#d9e9ec")
    right.plot(theta,enter,color="#235e77",label="Charge arrives")
    right.plot(theta,leave,color="#a44723",label="Opposite charge arrives")
    right.axhline(0,color="black",lw=.8,ls="--")
    right.set(xlabel="Angle from source (degrees)",ylabel="Time before horizon (microseconds)")
    right.legend(frameon=False,fontsize=8)
    fig.savefig(path)
    plt.close(fig)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--figure',type=Path)
    args=parser.parse_args()
    wall=wall_arrival()
    report=dict(shapes=[principal_readout(x) for x in ([1.,1.,1.],[3.,1.2,.6],[2.6,2.0,1.3])],
                ensembles=thermal_shapes(),matrix_wall=wall,interval_certificate=certify_pulse(),scalar_tide=ricci_transfer(36.),
                shell_flux=shell_force(),surface=dust_delivery(wall),all_outputs=inclusive_recovery(),
                angular_records=angular_records(),unresolved_rotor_energy=unresolved_rotor_energy())
    target=ROOT/'verification/cat-matter-ports-results.json'
    target.write_text(json.dumps(report,allow_nan=False,indent=2)+'\n',encoding='utf8')
    if args.figure:
        draw_figure(report,args.figure)
    print('Verified full matrix motion, signed regions, shell flux, scalar Jacobi flow, causal surface coverage and angular charge records.')
