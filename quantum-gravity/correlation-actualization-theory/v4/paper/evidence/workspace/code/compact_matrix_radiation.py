"""Four-dimensional zero modes of a slowly rotating BFSS source.

Time, radius and the source action in the radiation integrals are expressed
in units of the receiver frequency. The separate string example restores
the string length, D0 mass and four-dimensional Newton constant.
"""
import argparse
import json
from itertools import product
from math import exp, log, pi, sqrt
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]


def polarization_projection():
    # Three-dimensional angular integration, independent of the analytic moments.
    axis = np.array([1.,1j,0.])/sqrt(2)
    quad = np.outer(axis,axis)
    values = np.zeros(4)
    errors = []
    c_nodes,c_weights = leggauss(12)
    for c,weight in zip(c_nodes,c_weights):
        for phi in 2*pi*np.arange(24)/24:
            n = np.array([sqrt(1-c*c)*np.cos(phi),sqrt(1-c*c)*np.sin(phi),c])
            p = np.eye(3)-np.outer(n,n)
            transverse = p @ quad @ p
            longitudinal = n @ quad @ n
            # The eleventh direction carries the projected longitudinal momentum.
            lift = np.vstack([p,n])
            full = lift @ quad @ lift.T
            components = np.array([
                np.linalg.norm(transverse-p*np.trace(transverse)/2)**2,
                abs(longitudinal)**2*(1/2-1/8),
                2*np.linalg.norm(p @ quad @ n)**2,
                abs(longitudinal)**2*(1+1/8)])
            errors.append(max(abs(components.sum()-np.linalg.norm(full)**2),
                              abs(np.trace(full)),abs(np.linalg.norm(full)-1)))
            values += weight/48*components
    np.testing.assert_allclose(values,[2/5,1/20,2/5,3/20],atol=2e-14)
    assert max(errors) < 2e-14
    return dict(order=["helicity_two","volume_scalar","RR_vector","dilaton"],
                external_fractions=values.tolist(),max_projection_error=float(max(errors)))


def matrix_currents():
    # Evaluate the dielectric dipole directly from commutators, then compute
    # its Fourier radiation. The three planes have orthogonal matrix spins.
    size = 7
    j = (size-1)/2
    m = np.arange(size)-j
    raising = np.diag(np.sqrt((j-m[:-1])*(j+m[:-1]+1)),-1)
    spin = [(raising+raising.T)/2,(raising-raising.T)/(2j),np.diag(m)]
    casimir_trace=size*(size**2-1)/12
    for phase in (.13,.71,1.23):
        matrices = [[np.cos(phase)*q,np.sin(phase)*q] for q in spin]
        for i,jj,k in product(range(2),repeat=3):
            x,y,z = matrices[0][i],matrices[1][jj],matrices[2][k]
            dipole = (-1j*np.trace(x @ (y@z-z@y))/casimir_trace).real
            want = np.prod([[np.cos(phase),np.sin(phase)][v] for v in (i,jj,k)])
            assert abs(dipole-want)<2e-14

    n = 128
    phase = np.arange(n)*2*pi/n
    circle = np.array([np.cos(phase),np.sin(phase)])
    dipole = np.einsum("it,jt,kt->tijk",circle,circle,circle).reshape(n,8)
    bands = np.fft.fft(dipole,axis=0)/n
    frequencies = np.fft.fftfreq(n)*n
    weights = np.sum(abs(bands)**2,axis=1)*frequencies**4
    spectrum = {str(q):float(weights[abs(frequencies)==q].sum()) for q in (1,3)}
    np.testing.assert_allclose([spectrum["1"],spectrum["3"]],[.75,20.25],atol=2e-13)
    inertia,omega,grav = 1.,1.,1.
    tensor = 32/5*grav*inertia**2*omega**6
    metric = 3*16*grav*inertia**2*omega**6
    threeform = 4*grav*(inertia**2*omega**2/2)*sum(spectrum.values())*omega**4
    total = metric+threeform
    assert abs(total-90)<2e-12 and abs(tensor/total-16/225)<1e-13
    # The three-form dipole has one external and two internal indices.
    # Its external transverse and longitudinal pieces average to 2/3 and 1/3.
    d3=np.array([1.,2.,-1.])/sqrt(6)
    ncos,nweights=leggauss(10)
    transverse=0.
    for c,w in zip(ncos,nweights):
        for az in 2*pi*np.arange(16)/16:
            normal=np.array([np.sqrt(1-c*c)*np.cos(az),np.sqrt(1-c*c)*np.sin(az),c])
            transverse+=w/32*(1-abs(normal @ d3)**2)
    assert abs(transverse-2/3)<1e-14
    return dict(dipole_fourier_weight=spectrum,power_in_G_I2_Omega6=dict(
        tensor=tensor,complete_metric=metric,complete_threeform=threeform,RR_threeform=threeform*transverse,
        NS_twoform=threeform*(1-transverse),all=total),
        visible_tensor_fraction=tensor/total)


def source_reaction():
    # Compare the adiabatic first law with differential energy balance.
    rows=[]
    for x in (1.,.8,.4,.1,.025):
        b=(2/(1+x))**(1/6)
        energy=(1+2*x)*b**4/3
        spin=x*b**3
        t=(2/x-2-log(x))/4
        recovered=brentq(lambda z: 2/z-2-log(z)-4*t, .001,1.01)
        assert abs(recovered-x)<1e-12
        dxdt=-4*x*x/(2+x)
        dspin=b**3*(1-x/(2*(1+x)))
        denergy=b**4/3*(2-2*(1+2*x)/(3*(1+x)))
        p=x*x*b**10
        assert abs(dspin*dxdt+p/b)<3e-14
        assert abs(9*denergy*dxdt/4+p)<3e-14
        rows.append(dict(radial_ratio_squared=x,time_in_tensor_loss_units=t,
                         external_frequency_ratio=b,external_spin_ratio=spin,
                         remaining_excitation_fraction=energy,power_ratio=p))
    return dict(tensor_only=rows,residual_excitation=2**(2/3)/3,
                initial_scaled_chirps=dict(tensor_only=1/9,
                    ten_dimensional_metric=-71/72,eleven_dimensional_metric=-5/6,
                    all_IIA_bosonic=-25/16))


def emission_clock(w, strength):
    # t=phi=0 at crossing the receiver, whose frequency is one.
    return np.expm1(-6*np.log(w))/(60*strength), np.expm1(-5*np.log(w))/(50*strength)


def fourier_sweep(strength, distance, high, low):
    # Integrate in log frequency, separately on the positive and negative
    # frequency branches. Bound phase increments on each Gauss interval.
    nodes,weights=leggauss(12)
    span=log(high/low)
    phase_derivative=(low**-6+low**-5)/(5*strength)
    steps=max(8,int(np.ceil(span*phase_derivative/(2*pi))))
    step=span/steps
    accum=np.zeros(2,complex)
    for begin in range(0,steps,4096):
        starts=log(low)+step*np.arange(begin,min(steps,begin+4096))
        w=np.exp(starts[:,None]+step*(nodes+1)/2)
        t,phase=emission_clock(w,strength)
        for k,sign in enumerate((-1,1)):
            accum[k]+=step/2*np.sum(np.exp(2j*(t+sign*phase))*weights)
    dressed=4/(5*distance)*accum
    return float(3/8*np.sum(abs(dressed)**2))


def exact_receiver(strength,distance,high,low,tolerance):
    t0,_=emission_clock(high,strength)
    t1,_=emission_clock(low,strength)
    identity=np.eye(2)
    zero=np.zeros((2,2))
    def equation(t,y):
        u=1+60*strength*t
        phase=np.expm1(5/6*np.log(u))/(50*strength)
        c,s=np.cos(2*phase),np.sin(2*phase)
        tide=8*strength/distance/u*np.array([[c,s],[s,-c]])
        return (np.block([[zero,identity],[-identity+tide,zero]]) @ y.reshape(4,4)).ravel()
    sol=solve_ivp(equation,(t0,t1),np.eye(4).ravel(),method="DOP853",
                  rtol=tolerance,atol=tolerance*.01)
    assert sol.success
    m=sol.y[:,-1].reshape(4,4)
    a,b,c,d=m[:2,:2],m[:2,2:],m[2:,:2],m[2:,2:]
    pos=(a+d+1j*(c-b))/2
    neg=(a-d+1j*(c+b))/2
    symplectic=pos @ pos.conj().T-neg @ neg.conj().T
    err=float(np.max(abs(symplectic-identity)))
    assert err < 4e-8
    # det(U U^dagger)=det(1+V V^dagger). This evaluation also resolves
    # probabilities below the error in directly subtracting the quiet amplitude.
    singular=np.linalg.svd(neg,compute_uv=False)
    return float(-np.expm1(-1.5*np.log1p(singular**2).sum())),err


def receiving_histories():
    distance,high,low=30.,1.16,.86
    sweep=[]
    for strength in (.0008,.00025,.00008,.000016,.000004,.000001,.0000004):
        born=fourier_sweep(strength,distance,high,low)
        asymptotic=12*pi/5*strength/distance**2
        row=dict(strength=strength,dimensionless_distance=distance,detected=born,
                 full_stationary_phase=asymptotic,ratio=born/asymptotic)
        if strength in (.0008,.00025):
            first,_=exact_receiver(strength,distance,high,low,2e-10)
            fine,err=exact_receiver(strength,distance,high,low,3e-12)
            assert abs(fine/first-1)<2e-6 and abs(fine/born-1)<2e-4
            row.update(symplectic_probability=fine,symplectic_residual=err)
        sweep.append(row)
    assert abs(sweep[-1]["ratio"]-1)<.04
    angles=[]
    for c in (0.,.25,.5,.75,1.):
        plus,cross=(1+c*c)/2,c
        state=np.array([plus,1j*cross])
        opposite=state.conj()
        ss=abs(np.vdot(state,opposite))/np.vdot(state,state).real
        rate=(plus**2+cross**2)/2
        conclusive=rate*(1-ss)
        assert abs(conclusive-c*c)<1e-12
        angles.append(dict(cosine=c,pair_relative=rate,sign_overlap=ss,
                           conclusively_signed_relative=conclusive))
    return dict(sweeps=sweep,angles=angles)


def compact_example():
    size,coefficient,radius,gs=256,.02,15.,1e-16
    casimir_trace=size*(size**2-1)/12
    omega=sqrt(2)*coefficient/(2*pi)
    inertia=casimir_trace*coefficient**2/gs
    dimensionless_g=gs**2/(8*radius**6)
    strength=dimensionless_g*inertia*omega**3
    j=inertia*omega
    return dict(rank=size,matrix_length_in_string_units=coefficient,
                torus_radius_in_string_units=radius,string_coupling=gs,
                size_over_compact_radius=coefficient*sqrt(size**2-1)/(2*radius),
                strongest_harmonic_to_KK=3*omega*radius,dimensionless_chirp=strength,
                spin_times_sqrt_chirp=j*sqrt(strength),coherence_in_inverse_frequency=1/sqrt(10*strength),
                signed_probability_axial_at_50=12*pi/5*strength/50**2)


def local_record_bounds():
    rows=[]
    for c in (0.,.5,1.):
        a=(1+c*c)/2
        # Two reciprocal detecting vectors implement the optimal unambiguous
        # discrimination of the two equiprobable handed pair states.
        basis=np.array([[a,1j*c],[a,-1j*c]],complex).T
        detectors=np.array([[c,-1j*a],[c,1j*a]])/(np.sqrt(2)*a)
        effect=detectors.conj().T @ detectors
        assert np.linalg.eigvalsh(np.eye(2)-effect).min()>-1e-14
        amplitude=detectors @ basis
        assert np.max(abs(amplitude-np.diag(np.diag(amplitude))))<1e-14
        np.testing.assert_allclose(abs(amplitude[0,0])**2/2,c*c,atol=1e-14)
        # A classical sign leaves an otherwise unmeasured payload intact.
        eta=.25*c*c
        conditional=[np.sqrt(1-eta)*np.eye(2),np.sqrt(eta)*np.diag([1,0]),
                     np.sqrt(eta)*np.diag([0,1])]
        fidelity=sum(abs(np.trace(k))**2 for k in conditional)/4
        np.testing.assert_allclose(fidelity,1-eta/2)
        rows.append(dict(cosine=c,example_sign_probability=eta,recorded_sign_fidelity=fidelity))
    return dict(sign_readers=rows,weak_shell_example_expected_signs_upper=2*pi/5*.1*.01**2/50)


def adopted_parent():
    # The material control is a degree of freedom of the joint state. Construct
    # the routing unitary once, before preparing any incoming density operator.
    eye = np.eye(2, dtype=complex)
    swap = np.array([[0, 1], [1, 0]], dtype=complex)
    compatible = np.diag([1., 0.]).astype(complex)
    incompatible = eye - compatible
    route = np.kron(compatible, eye) + np.kron(incompatible, swap)
    np.testing.assert_array_equal(route.conj().T @ route, np.eye(4))
    # Input and an independent reference share a Bell state, so any relative
    # phase loss at the surface would be visible in this test.
    payload = np.array([1., 0., 0., 1.], dtype=complex)/sqrt(2)
    bell = np.outer(payload, payload.conj())
    received_charge = np.array([1., 1j], dtype=complex)/sqrt(2)
    control = np.outer(received_charge, received_charge.conj())
    incident = np.diag([1., 0.])
    initial = np.kron(np.kron(control, incident), bell)
    output = np.zeros_like(initial)
    branches = []
    for effect in (compatible, incompatible):
        local = np.kron(route @ np.kron(effect, eye), np.eye(4))
        branch = local @ initial @ local.conj().T
        output += branch
        port = np.trace(branch.reshape(2, 2, 4, 2, 2, 4), axis1=0, axis2=3)
        branches.append(np.trace(port, axis1=1, axis2=3).diagonal().real.tolist())
    np.testing.assert_allclose(branches, [[.5, 0.], [0., .5]], atol=2e-15)
    after = np.trace(output.reshape(4, 4, 4, 4), axis1=0, axis2=2)
    assert abs(np.vdot(payload, after @ payload)-1) < 2e-15
    # Noncommuting material preparations test the operator-order lower bound
    # using the smallest generalized eigenvalue, independent of any routing.
    from scipy.linalg import eigvalsh
    rho_a = np.diag([.8, .2])
    rotation = np.array([[1.,-1.],[1.,1.]])/sqrt(2)
    rho_b = rotation @ np.diag([.65, .35]) @ rotation.T
    beta = float(eigvalsh(rho_b, rho_a)[0])
    assert np.linalg.eigvalsh(rho_b-beta*rho_a)[0] > -3e-15
    assert np.linalg.eigvalsh(rho_b-(beta+1e-7)*rho_a)[0] < -1e-9
    for angle in np.linspace(0,pi,97):
        v = np.array([np.cos(angle), np.sin(angle)])
        assert v @ rho_b @ v >= beta*(v @ rho_a @ v)-3e-15
    exact = []
    for d, k in ((2, 1), (2, 5), (2, 10), (3, 3)):
        # Each sector stores the k causal pairs already delivered. Enumerate
        # all finite pairs, independent of the analytic d**(-k) expression.
        strings = np.arange(d**k)
        matched_count = np.equal.outer(strings, strings).sum()
        measured = float(matched_count/len(strings)**2)
        assert measured == d**(-k)
        exact.append(dict(alphabet=d, pairs=k, near_transmission=1.,
                          distant_transmission=measured, compulsory_defect_transmission=0.))
    # An active wall either transfers between equal-energy ports or is absent.
    # Check recoil on shell independently of the small-gap approximation.
    for mass, gap in ((1., .125), (5., 1.2), (150., .8)):
        energy = gap+gap**2/(2*mass)
        np.testing.assert_allclose(sqrt((mass+gap)**2+energy**2),mass+energy,rtol=2e-15)
    return dict(conditional_route_masses=branches,
                spectator_entanglement_fidelity=float(np.vdot(payload,after@payload).real),
                noncommuting_order_floor=beta, finite_receipts=exact)


def cat_matrix_forms():
    """Compare the two microscopic descriptions on the same material clock."""
    sigma_x = np.array([[0,1],[1,0]],complex)
    sigma_z = np.diag([1.,-1.])
    theta = 2*pi*np.arange(256)/256
    # X1 = cos(theta)*sigma_x, X2 = (1/2)sin(theta)*sigma_z. An
    # explicit covariant clock commutator is compared with its Fourier limit.
    dx2 = (2*np.sin(theta)**2 + .5*np.cos(theta)**2)
    comm2 = 2*np.cos(theta)**2*np.sin(theta)**2
    target = float(np.mean((dx2+comm2)/2))
    rows = []
    for count in (6,12,24,48):
        clock = np.kron(np.diag(np.arange(count)), np.eye(2))
        shift = np.diag(np.ones(count-1),-1)
        x = np.kron((shift+shift.T)/2,sigma_x)
        y = np.kron((shift-shift.T)/(4j),sigma_z)
        pairs = ((clock,x),(clock,y),(x,y))
        euclidean = sum(np.linalg.norm(a@b-b@a)**2 for a,b in pairs)/(2*count)
        kinetic = sum(np.linalg.norm(clock@z-z@clock)**2 for z in (x,y))/(2*count)
        np.testing.assert_allclose(kinetic, .625*(1-1/count),atol=3e-15)
        rows.append(dict(clock_rank=count,
                         euclidean_action_per_clock=float(euclidean),
                         infinite_clock_action=target))
    assert all(abs(r["euclidean_action_per_clock"]-target)>abs(s["euclidean_action_per_clock"]-target)
               for r,s in zip(rows,rows[1:]))
    # Continuum circle arcs compressed to a finite relative-charge space.
    # Direct integration provides an independent Gram-matrix construction.
    angle, weight=leggauss(64)
    arcs=[]
    for budget in (1,3,7,11):
        n=np.arange(budget+1)
        diff=n[:,None]-n[None,:]
        half=.5*np.sinc(diff/2)  # integral on [-pi/2,pi/2], divided by 2*pi
        waves=np.exp(1j*angle[:,None]*pi/2*n[None,:])
        np.testing.assert_allclose(half,waves.conj().T@(weight[:,None]*waves)/4,atol=4e-15)
        eigens=np.linalg.eigvalsh(half)
        assert 0<eigens[0] and eigens[-1]<1
        np.testing.assert_allclose(eigens[0],1-eigens[-1],atol=6e-16)
        if budget==1:
            np.testing.assert_allclose(eigens[0],.5-1/pi,atol=2e-16)
        arcs.append(dict(total_charge=budget,best_wrong_half=float(eigens[0])))
    # Relative charge transforms with the material reference. Check elementary
    # S and T transformations, including both signs and offset compensation.
    signed=lambda u,v: int(u[0]*v[1]-u[1]*v[0])
    S=np.array([[0,-1],[1,0]])
    T=np.array([[1,1],[0,1]])
    for g in (S,T,S@T,T@S@T,np.linalg.matrix_power(T,-3).astype(int)):
        for ell in (np.array([1,0]),np.array([2,-1])):
            for v in (np.array([0,1]),np.array([-3,2])):
                assert signed(g@ell,g@v)==signed(ell,v)
    # A rectangular spacelike T duality maps momentum to winding.
    ls,rs,gs=.75,2.5,.4
    rb,gb,r11=ls**2/rs, gs*ls/rs, gs*ls
    for m,n in ((1,0),(0,1),(2,-3)):
        np.testing.assert_allclose(np.hypot(m/rs,n/r11), rb/ls**2*np.hypot(m,n/gb))
    # Measured visibility gives a conservative bound using V0<=1. Values
    # from a paper-specific benchmark are kept separate from unknown CAT rates.
    eta_envelope=(1.5+1.96*np.hypot(2.3,1.5))*1e-15
    cassini_cap=sqrt(7e-5/(2-7e-5))
    return dict(clock=rows,circle_arcs=arcs,duality_mass_controls=[1/rs,1/r11],
                microscope_illustrative_envelope=float(eta_envelope),
                cassini_scalar_cap=cassini_cap)


def geometry():
    grades=[]
    for r in (.5,1.,2.,5.):
        for charges in ((1.,1.,1.,1.),(.3,.6,1.3,2.)):
            def area(t): return np.prod(t+np.array(charges))**.25
            h=1e-3*r
            numerical=(-area(r+2*h)+16*area(r+h)-30*area(r)+16*area(r-h)-area(r-2*h))/(12*h*h)
            signed=-np.var(1/(r+np.array(charges)))
            assert abs(numerical/area(r)-signed)<2e-8
        def funnel(z): return (z**4+1.)**.25
        curvature=3*r*r/(r**4+1)**2
        h=1e-3*r
        numerical=(-funnel(r+2*h)+16*funnel(r+h)-30*funnel(r)+16*funnel(r-h)-funnel(r-2*h))/(12*h*h)
        assert abs(numerical/funnel(r)-curvature)<2e-8
        grades.append(dict(r=r,funnel_Rdd_over_R=curvature,unequal_four_charge_Rdd_over_R=signed))
    required=[]
    for r in (1.00001,1.1,1.5,3.,15.,1000.):
        f=1-1/r
        a=sqrt(f)/r
        deriv=-1/r+1.5/r**2
        effective=f*(1/r**2-3/r**3)+deriv**2+2*f/r*deriv-2*a*a
        assert abs(effective-(-2/r**2+2.25/r**4))<1e-14
        required.append(dict(r_over_horizon=r,angular_barrier=a*a,required_mass_squared=effective))
    return dict(radial_convergence=grades,neutral_angular_requirement=required)


def figure(report,path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,(a,b)=plt.subplots(1,2,figsize=(8.2,3.05),layout="constrained")
    s=np.linspace(0,1.4,180)
    x=np.array([brentq(lambda x: 2/x-2-log(x)-4*t,.04,1.01) for t in s])
    a.plot(s,(2/(1+x))**(1/6),label="Tensor alone")
    a.plot(s,(1+75*s/8)**(-1/6),label="All bosonic zero modes")
    a.set(xlabel="Retarded time / initial tensor loss time",ylabel="Source frequency / initial value")
    a.legend(frameon=False,fontsize=8)
    c=np.linspace(0,1)
    b.plot(c,((1+c**2)**2/4+c*c)/2,label="Pair received")
    b.plot(c,c*c,label="Sign identified")
    b.set(xlabel="Absolute cosine of viewing angle",ylabel="Probability / axial value")
    b.legend(frameon=False,fontsize=8)
    fig.savefig(path)
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    report=dict(polarization=polarization_projection(),currents=matrix_currents(),
                reaction=source_reaction(),receipts=receiving_histories(),example=compact_example(),
                geometry=geometry(),material_records=local_record_bounds(),
                adopted_action=adopted_parent(),cat_matrix_forms=cat_matrix_forms())
    dest=ROOT/"verification/compact-matrix-radiation-results.json"
    dest.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        figure(report,args.figure)
    print("Compactified matrix currents, secular reaction, independent receiver and radial geometry verified.")
