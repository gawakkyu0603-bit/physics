"""Finite-fall gravity, all-output recovery and matrix geometry of CAT.

All occurrence probabilities in this file concern the stated physical
preparation. A missing material index crossing is never treated as a write.
"""
import argparse
import json
from math import cos, exp, factorial, log, pi, sqrt
from pathlib import Path

import numpy as np
from numpy.polynomial.laguerre import laggauss
from scipy import constants, linalg, optimize
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[1]
SOLAR_GM = 1.3271244e20   # IAU nominal solar mass parameter, m^3 s^-2
HBAR = constants.hbar
C = constants.c


def clifford_generators():
    pauli_x = np.array([[0.,1.],[1.,0.]])
    pauli_y = np.array([[0.,-1j],[1j,0.]])
    pauli_z = np.diag([1.,-1.])
    def tensor(factors):
        out=np.array([[1.]])
        for factor in factors:
            out=np.kron(out,factor)
        return out
    gamma=[tensor([pauli_z]*j+[p]+[np.eye(2)]*(3-j))
           for j in range(4) for p in (pauli_x,pauli_y)]+[tensor([pauli_z]*4)]
    for i,x in enumerate(gamma):
        np.testing.assert_array_equal(x.conj().T,x)
        for j,y in enumerate(gamma):
            np.testing.assert_array_equal(x@y+y@x,2*(i==j)*np.eye(16))
    return dict(spinor_dimension=16,spatial_generators=len(gamma),ten_generator_minimum=2**5)


def receiver_windows(horizon_time):
    # Ingoing radial light has constant advanced time. A hovering surface
    # measures the advanced-time interval multiplied by its own lapse.
    from scipy.integrate import quad
    def primitive(x):
        z=sqrt(x)
        return 2*(z**3/3-z**2/2+z-log(1+z))
    rows=[]
    for x in (1.,1.0001,1.01,1.1):
        part=primitive(1.2)-primitive(x)
        np.testing.assert_allclose(part,quad(lambda y:y/(1+sqrt(y)),x,1.2)[0],rtol=2e-13)
        advanced=1.5*horizon_time*part
        rows.append(dict(receiver_radius_over_rs=x,advanced_margin_s=advanced,
                         static_proper_margin_s=advanced*sqrt(1-1/x) if x>1 else None))
    return rows


def jacobi_basis(u):
    return np.array([[u**(4/3), u**(-1/3)], [-4*u**(1/3)/3, u**(-4/3)/3]])


def jacobi_transfer(radius_ratio):
    # u is remaining time to the classical singularity, divided by its value
    # at the readout. The coordinates are (separation, u_final * local velocity).
    s = sqrt(radius_ratio)
    u_i = s**3
    fall = jacobi_basis(1.) @ linalg.inv(jacobi_basis(u_i))
    free = np.array([[1., u_i-1], [0., 1.]])
    relative = fall @ linalg.inv(free)
    stable_trace = 2-(s+1/s-2)**2*((s+1/s)**2+4*(s+1/s)+8)/15
    np.testing.assert_allclose(np.trace(relative), stable_trace, atol=4e-13)
    np.testing.assert_allclose(linalg.det(relative), 1., atol=6e-13)
    return fall, free, relative


def gravitational_reader():
    threshold = optimize.brentq(lambda k: np.trace(jacobi_transfer(k)[2])+2, 9, 10)
    records = []
    for ratio in (1.5, 4., 9., 10., 16.):
        fall, free, relative = jacobi_transfer(ratio)
        start = ratio**1.5
        def geodesic(u, vector):
            x, v = vector
            return [-v, -4*x/(9*u*u)]
        numerical = np.column_stack([solve_ivp(geodesic, (start, 1.), column,
            rtol=2e-11, atol=2e-13, method="DOP853").y[:,-1] for column in np.eye(2)])
        np.testing.assert_allclose(fall, numerical, rtol=8e-11, atol=4e-10)
        row = dict(radius_ratio=ratio, relative_trace=float(np.trace(relative)))
        if ratio>threshold:
            values, vectors = linalg.eig(relative.T)
            index = int(np.argmin(values.real))
            lam = float(values[index].real)
            quad = vectors[:,index].real
            if quad[0]<0:
                quad = -quad
            quad /= linalg.norm(quad)
            np.testing.assert_allclose(quad @ fall, lam*(quad @ free), atol=1e-12)
            row.update(scale=lam, measured_quadrature=quad.tolist(),
                       incoming_quadrature=(quad @ free).tolist())
        records.append(row)
    u_h=4*10*SOLAR_GM/(3*C**3)
    u_f=u_h*1.2**1.5
    return dict(critical_ratio=threshold, examples=records,
                surface_windows=receiver_windows(u_h),ten_solar_masses=dict(start_radius_over_rs=19.2,readout_radius_over_rs=1.2,
                                      fall_time_s=63*u_f,lead_before_horizon_s=u_f-u_h))


def perturbed_tides():
    """Local vacuum tidal histories in a parallel frame, at radius ratio 16."""
    first = np.array([[0.,1.,.3],[1.,0.,-.4],[.3,-.4,0.]])
    second = np.array([[.2,0.,-.5],[0.,-.1,.7],[-.5,.7,-.1]])
    eye, zero = np.eye(3), np.zeros((3,3))
    flat = np.block([[eye,63*eye],[zero,eye]])
    symplectic = np.block([[zero,eye],[-eye,zero]])
    rows = []
    for amplitude in (0.,.02,.05,.15):
        def system(u, values):
            shear = np.sin(np.log(u))*first + np.cos(np.log(u))*second
            tide = (np.diag([4.,-2.,-2.])/9 + amplitude*shear)/u**2
            return (np.block([[zero,-eye],[-tide,zero]])@values.reshape(6,6)).ravel()
        fall = solve_ivp(system,(64.,1.),np.eye(6).ravel(),method="DOP853",
                         rtol=2e-11,atol=2e-13).y[:,-1].reshape(6,6)
        relative = fall@linalg.inv(flat)
        np.testing.assert_allclose(relative.T@symplectic@relative,symplectic,atol=3e-8)
        eig, vec = linalg.eig(relative.T)
        j = np.argmin(eig.real)
        assert abs(eig[j].imag)<1e-9 and eig[j].real<-1
        lam = float(eig[j].real)
        quad = vec[:,j].real
        np.testing.assert_allclose(quad@fall,lam*(quad@flat),rtol=2e-9,atol=2e-9)
        rows.append(dict(amplitude=amplitude,negative_eigenvalue=lam))
    return rows


def integral_tail(order, x):
    # Laplace representation of an oscillatory inverse-power tidal tail.
    nodes, weights = laggauss(48)
    return np.dot(weights,nodes**(order-1)/(nodes+1j*x))/factorial(order-1)


def ordinary_matter():
    mu = constants.physical_constants["proton mass"][0]/2
    length = .74144e-10                  # H2 equilibrium separation, m
    omega = 2*pi*C*100*4401.21          # spectroscopic wavenumber, cm^-1
    rows=[]
    for mass in (3.,10.,1.e6):
        u=4*mass*SOLAR_GM/(3*C**3)
        x=omega*u
        j=abs(integral_tail(3,x))
        displacement=32*mu*length**2*j**2/(81*HBAR*omega**3*u**4)
        squeeze=2*abs(integral_tail(3,2*x))**2/(81*x**4)
        assert abs(j*x-1)<3e-9
        row=dict(solar_masses=mass,omega_times_deadline=x,
                 radial_single_displacement=displacement,radial_pair_leading=squeeze)
        for body,kg in (("70kg",70.),("1p31microgram",1.31e-9)):
            row[body+"_mean_excited"]=(displacement+squeeze)*kg/(4*mu)/5
        rows.append(row)
    # Independent nonadiabatic forced oscillator at moderate dimensionless x.
    x=10.
    ui=250.
    def derivative(u,y):
        return np.array([-y[1], x*x*y[0]-1/u**2])
    y0=[1/(ui**2*x**2), 2/(ui**3*x**2)]
    end=solve_ivp(derivative,(ui,1),y0,rtol=3e-11,atol=1e-13,method="DOP853").y[:,-1]
    excitation=abs((end[0]-1/x**2)+1j*end[1]/x)
    np.testing.assert_allclose(excitation,2*abs(integral_tail(3,x))/x**2,rtol=5e-7)
    return rows


def spin_matrices(j):
    m=np.arange(-j,j+1)
    up=np.diag(np.sqrt((j-m[:-1])*(j+m[:-1]+1)),-1)
    return (up+up.T)/2, (up-up.T)/(2j), np.diag(m)


def angular_channel(jout,jcore):
    # Couple the outgoing partial wave and remaining core to total j=1/2.
    # Angular matrices are built independently of tabulated Clebsch coefficients.
    a,b=spin_matrices(jout),spin_matrices(jcore)
    total=[np.kron(x,np.eye(b[0].shape[0]))+np.kron(np.eye(a[0].shape[0]),y)
           for x,y in zip(a,b)]
    casimir=sum(x@x for x in total)
    keep=np.flatnonzero(abs(np.diag(total[2])-.5)<1e-12)
    spec,states=linalg.eigh(casimir[np.ix_(keep,keep)])
    pos=np.argmin(abs(spec-.75))
    assert abs(spec[pos]-.75)<2e-14
    plus=np.zeros(len(casimir),complex)
    plus[keep]=states[:,pos]
    minus=(total[0]-1j*total[1])@plus
    v=np.column_stack([minus,plus])
    np.testing.assert_allclose(v.conj().T@v,np.eye(2),atol=2e-15)
    for axis in range(3):
        np.testing.assert_allclose(total[axis]@v,v@spin_matrices(.5)[axis],atol=2e-15)
    return v


def recovery():
    species=[("spinor",.5,0.,.5),("photon",1.,.5,.3),("graviton",2.,1.5,.2)]
    blocks=[sqrt(prob)*angular_channel(j,jc) for _,j,jc,prob in species]
    emitted=np.vstack(blocks)
    np.testing.assert_allclose(emitted.conj().T@emitted,np.eye(2),atol=2e-15)
    # A source-independent scalar charge has two Born readings. A biased
    # charge is recorded on the whole quantum state before the emission.
    tests=[]
    for bias in (0.,.2,.7,1.):
        effects=[np.diag([(1+bias)/2,(1-bias)/2]),
                 np.diag([(1-bias)/2,(1+bias)/2])]
        kraus=[emitted@np.diag(np.sqrt(np.diag(a))) for a in effects]
        exact=sum(np.sum(linalg.svdvals(k))**2 for k in kraus)/4
        state=np.array([1.,0.,0.,1.])/sqrt(2)
        fixed=sum((np.kron(np.eye(2),emitted.conj().T@k)@np.outer(state,state)
                   @np.kron(np.eye(2),emitted.conj().T@k).conj().T) for k in kraus)
        np.testing.assert_allclose(exact,float(np.vdot(state,fixed@state).real),atol=1e-14)
        np.testing.assert_allclose(exact,(1+sqrt(1-bias**2))/2)
        tests.append(dict(charge_bias=bias,all_output_entanglement_fidelity=float(exact)))
    return dict(species_test_weights={name:prob for name,_,_,prob in species},
                channel_output_dimension=emitted.shape[0],record_tests=tests)


def angular_receipt():
    """Ordinary Newtonian sector of the CAT mass-quadrupole coupling.

    Use the l=1 rotor wavefunctions to calculate the receiving amplitudes,
    before the common CAT occupied/vacuum charge projection.
    """
    from numpy.polynomial.legendre import leggauss
    cos_theta, weights=leggauss(12)
    phi=2*pi*np.arange(24)/24
    z, az=np.meshgrid(cos_theta,phi,indexing="ij")
    radial=np.sqrt(1-z*z)
    axis=np.stack([radial*np.cos(az),radial*np.sin(az),z],axis=-1)
    harmonics=[sqrt(3/(8*pi))*radial*np.exp(-1j*az),sqrt(3/(4*pi))*z,
               -sqrt(3/(8*pi))*radial*np.exp(1j*az)]
    measure=weights[:,None]*2*pi/len(phi)
    tensor=axis[:,:,:,None]*axis[:,:,None,:]-np.eye(3)/3
    def element(final,initial):
        weighted=measure*harmonics[final+1].conj()*harmonics[initial+1]
        return np.einsum('ab,abij->ij',weighted,tensor)
    diagonal=np.array([element(m,m)[2,2].real for m in (-1,0,1)])
    np.testing.assert_allclose(diagonal,[-2/15,4/15,-2/15],atol=1e-14)
    source=element(-1,1)
    detector=element(1,-1)
    shift=np.array([1,-1j,0])
    np.testing.assert_allclose(shift@source@shift,-4/5,atol=1e-14)
    # For the two transverse traceless tensors only the paired deltas in
    # the fourth derivative of 1/R contribute, with coefficient six.
    exchange=-1.5*np.sum(source*detector)
    np.testing.assert_allclose(exchange,-6/25,atol=1e-14)
    strength=log(2)
    vac=np.exp(-strength*(diagonal/(-2/15))**2)
    p=1-vac
    return_fid=(1+sqrt(vac[0]*vac[1])+sqrt(p[0]*p[1]))/2
    assert abs(p[2]-p[0])<1e-14
    mu=constants.physical_constants["proton mass"][0]/2
    length=.74144e-10
    omega=2*pi*C*100*4401.21
    bond_element=2*length*sqrt(HBAR/(2*mu*omega))
    separation=1e-8
    coupling=6*constants.G*(mu*bond_element)**2/(25*HBAR*separation**5)
    # Exponentiating the full resonant two-channel Hamiltonian checks the
    # ideal bright and dark charge response without fitting a readout bias.
    angle=.37
    v=linalg.expm(-1j*np.array([[0.,angle],[angle,0.]]))[:,0]
    click=float(abs(v[1])**2)
    np.testing.assert_allclose(click,np.sin(angle)**2,atol=1e-14)
    # A freely contracting spin-one matrix sphere sweeps the actual CAT
    # index wall. The same clock fixes the duration available for exchange.
    from scipy.integrate import quad
    scale0=1.
    port_radius=.5
    def contraction(time,state):
        return [state[1],-2*state[0]**3]
    def crossing(time,state):
        return state[0]-port_radius
    crossing.terminal=True
    run=solve_ivp(contraction,(0.,2.),[scale0,0.],events=crossing,method="DOP853",
                  rtol=2e-12,atol=2e-14)
    wall_time=run.t_events[0][0]
    integration,_=quad(lambda u: 1/sqrt(1-u**4),port_radius,1.)
    np.testing.assert_allclose(wall_time,integration,rtol=2e-11)
    pauli=[2*m for m in spin_matrices(.5)]
    def matrix_index(scale):
        triple=[scale*m for m in spin_matrices(1.)]
        triple[2]=triple[2]-port_radius*np.eye(3)
        op=sum(np.kron(p,x) for p,x in zip(pauli,triple))
        return np.sum(np.sign(linalg.eigvalsh(op)))/2
    indices=[matrix_index(.51),matrix_index(.49)]
    assert indices==[1.,0.]
    # Columns are the two unknown sign states. Rows label source and receiver
    # port together, with an occupied row routed to the shifted physical charge.
    pair_h=np.zeros((3,3))
    pair_h[0,2]=pair_h[2,0]=.4
    scattering=linalg.expm(-1j*wall_time*pair_h)
    injection=np.eye(3)[:,:2]
    effect=injection.T@scattering.conj().T@np.diag([0.,0.,1.])@scattering@injection
    predicted=np.sin(.4*wall_time)**2
    np.testing.assert_allclose(effect,np.diag([predicted,0.]),atol=1e-14)
    wall=dict(radius_over_initial=.5,arrival_matrix_units=float(wall_time),
              index_before_after=[int(k) for k in indices],coupling_over_scale=.4,
              signed_charge_effect_diagonal=np.diag(effect).real.tolist())
    return dict(matrix_wall=wall,projected_axial_moment=diagonal.tolist(),transverse_exchange_factor=float(exchange.real),
                axial_mean_displacement_strength=strength,axial_click_probabilities=p.tolist(),
                axial_abs_m_fidelity=return_fid,axial_signed_m_fidelity=1.,
                axial_outcome_biases=dict(click=(p[1]-p[0])/(p[1]+p[0]),
                                         vacuum=(vac[0]-vac[1])/(vac[0]+vac[1])),
                chiral_pulse_area=angle,chiral_click_bright=click,chiral_click_dark=0.,
                chiral_entanglement_fidelity=(1+sqrt(1-click))/2,
                harmonic_hydrogen_example=dict(separation_m=separation,angular_frequency_s=omega,
                    transition_r_squared_m2=bond_element,exchange_per_second=coupling,
                    ideal_one_second_click=float(np.sin(coupling)**2)))


def matrix_geometry():
    metric=np.diag([-1.,1.,1.,1.])
    theta=np.array([[0.,2.,0.,0.],[-2.,0.,0.,0.],[0.,0.,0.,3.],[0.,0.,-3.,0.]])
    effective=theta.T@metric@theta
    np.testing.assert_array_equal(effective,np.diag([4.,-4.,9.,9.]))
    rows=[]
    for size in (32,64,128,256):
        grid=np.arange(size)
        line=4*(size/(2*pi))**2*np.sin(pi*grid/size)**2
        for s in (.035,.075):
            weights=np.exp(-s*line)
            ds=2*s*4*(weights@line)/weights.sum()
            rows.append(dict(unitary_period=size,diffusion=s,spectral_dimension=float(ds)))
    # Check the spectrum against actual clock and shift matrix commutators.
    size=7
    shift=np.roll(np.eye(size,dtype=complex),1,axis=0)
    clock=np.diag(np.exp(2j*pi*np.arange(size)/size))
    generators=[(u+u.conj().T)/2 for u in (shift,clock)]+[
        (u-u.conj().T)/(2j) for u in (shift,clock)]
    comm=lambda x,y: x@y-y@x
    for m,k in ((0,0),(1,2),(4,3)):
        v=np.linalg.matrix_power(clock,m)@np.linalg.matrix_power(shift,k)
        lhs=sum(comm(u,comm(u,v)) for u in generators)
        np.testing.assert_allclose(lhs,4*(np.sin(pi*m/size)**2+np.sin(pi*k/size)**2)*v,atol=4e-14)
    return dict(probe_metric_diagonal=np.diag(effective).tolist(),heat_traces=rows)


def relational_history():
    # The polar part of b-dagger times a gives the shift on a finite material
    # exchange ladder, including its physical source and sink.
    budget=3
    forward=np.diag([sqrt((r+1)*(budget-r)) for r in range(budget)],-1)
    shift=forward@linalg.pinv(np.diag(np.sqrt(np.diag(forward.T@forward))))
    np.testing.assert_allclose((np.eye(4)-shift@shift.T),np.diag([1.,0.,0.,0.]),atol=5e-16)
    np.testing.assert_allclose(np.linalg.matrix_power(shift,4),0)
    boundary=np.diag([1.,0.])
    h=np.array([[.1,.3],[.3,.4]])
    links=np.array([[.25,.15],[.3,-.1]])
    interior=np.diag([.65,-1.2])
    reactance=h-links@linalg.solve(interior,links.T)
    lhs=np.eye(2)+1j*reactance
    rhs=np.eye(2)-1j*reactance
    u=linalg.solve(lhs,rhs,assume_a="gen")
    np.testing.assert_allclose(lhs@u,rhs,rtol=0.,atol=2e-15)
    np.testing.assert_allclose(u.conj().T@u,np.eye(2),atol=2e-15)
    effects=[boundary,np.eye(2)-boundary]
    operators=[np.kron(shift,p@u) for p in effects]
    inlet=np.kron(np.diag([1.,0.,0.,0.]),boundary)
    step=lambda omega:sum(k@omega@k.conj().T for k in operators)
    hist=inlet.copy()
    for _ in range(budget):
        hist=inlet+step(hist)
    np.testing.assert_allclose(hist,inlet+step(hist),atol=1e-15)
    slices=hist.reshape(4,2,4,2)
    state=boundary.copy()
    for j in range(budget+1):
        np.testing.assert_allclose(slices[j,:,j,:],state,atol=2e-15)
        state=sum(p@u@state@u.conj().T@p for p in effects)
    return dict(material_ticks=budget,history_trace=float(np.trace(hist).real),
                final_port_population=float(slices[-1,1,-1,1].real))


def predictions():
    rates=[]
    for pulses in (1,2,4,8,20):
        angle=pi/(2*pulses)
        u=np.array([[cos(angle),-np.sin(angle)],[np.sin(angle),cos(angle)]])
        rho=np.diag([1.,0.])
        for _ in range(pulses):
            rho=np.diag(np.diag(u@rho@u.T))
        exact=(1-cos(pi/pulses)**pulses)/2
        np.testing.assert_allclose(rho[1,1],exact,atol=3e-15)
        rates.append(dict(occupied_readings=pulses,excitation=float(exact)))
    m,L,w,t=1e-9,.01,2*pi*100,1.
    target=sqrt(8*HBAR*w*log(2)/m)/(L*t)
    thermal=constants.k*.01*t/HBAR
    bell=np.array([0.,1.,1.,0.])/sqrt(2)
    total=[np.diag(np.asarray([0,1,1,2])==occupation).astype(float) for occupation in range(3)]
    separate=[np.diag(np.arange(4)==j).astype(float) for j in range(4)]
    def returned_fidelity(projectors,state):
        density=np.outer(state,state.conj())
        return float(np.vdot(state,sum(p@density@p for p in projectors)@state).real)
    shared=returned_fidelity(total,bell)
    apart=returned_fidelity(separate,bell)
    np.testing.assert_allclose([shared,apart],[1.,.5])
    angles=[]
    for theta in (0.,pi/6,pi/4,pi/2):
        v=np.array([cos(theta/2),np.sin(theta/2)])
        up=np.outer(v,v)
        pr=returned_fidelity([up,np.eye(2)-up],np.array([1.,0.]))
        np.testing.assert_allclose(pr,(1+cos(theta)**2)/2)
        angles.append(dict(angle_rad=theta,survival=pr))
    tri=returned_fidelity([np.diag(np.arange(3)==k) for k in range(3)],np.ones(3)/sqrt(3))
    np.testing.assert_allclose(tri,1/3)
    driver_mass=target*.10**4/(6*constants.G*.001)
    return dict(collective_bell_fidelity=shared,separate_bell_fidelity=apart,
                angle_scan=angles,three_letter_return=tri,point_source_mass_kg=driver_mass,
                balanced_return=.5,zeno=rates,gravity_gradient_s2=target,
                thermal_single_event_quality=thermal,
                coherent_occupation_scan=[dict(n=n,return_loss=2*exp(-n)*(1-exp(-n)))
                                          for n in (.1,log(2),2.,5.)])


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    report=dict(clifford=clifford_generators(),fall=gravitational_reader(),perturbed=perturbed_tides(),hydrogen=ordinary_matter(),recovery=recovery(),
                angular_receipt=angular_receipt(),geometry=matrix_geometry(),material_history=relational_history(),predictions=predictions())
    path=ROOT/"verification/cat-relational-collapse-results.json"
    path.write_text(json.dumps(report,allow_nan=False,indent=2)+"\n",encoding="utf8")
    if args.figure:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        fig,(a,b)=plt.subplots(1,2,figsize=(8.4,3.0),layout="constrained")
        k=np.linspace(1,16,150)
        a.plot(k,[np.trace(jacobi_transfer(q)[2]) for q in k],color="#214c69")
        a.axhline(-2,color="#944420",ls="--")
        a.axvline(report["fall"]["critical_ratio"],color="#944420",ls=":")
        a.set(xlabel="Radii ratio (start / readout)",ylabel="Trace of relative tidal map")
        n=np.linspace(0,5,150)
        b.plot(n,2*np.exp(-n)*(1-np.exp(-n)),color="#214c69",label="One occupied crossing")
        b.axhline(0,color="#555555",ls="--",label="Coherent return")
        b.set(xlabel="Mean gravitational excitation",ylabel="Return failure probability")
        b.legend(frameon=False,fontsize=8)
        fig.savefig(args.figure);plt.close(fig)
    print("CAT relational clock, tidal matter, recovery, dimensions and differential tests verified.")
