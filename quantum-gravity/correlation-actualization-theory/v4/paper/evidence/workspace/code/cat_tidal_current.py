"""Charge transported by the occupied tidal spectrum of a magnetized matrix receiver."""
import json
from pathlib import Path

import numpy as np
from scipy.constants import G, c, hbar
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigh, eigh_tridiagonal, solve_banded
from scipy.optimize import brentq
from scipy.special import erf, roots_legendre

from cat_tidal_crossing import evolve_receiver


SX = np.array([[0, 1], [1, 0]], dtype=complex)
SY = np.array([[0, -1j], [1j, 0]], dtype=complex)
SZ = np.diag([1., -1.]).astype(complex)
I2 = np.eye(2, dtype=complex)
MULTIPLICITY = np.array([2., 1., 1.])


def prepare(q=.3):
    profile = evolve_receiver(q)
    flat = solve_ivp(lambda t,z: [z[1],-2*q*q*z[0]**3],(0.,1.),(1.,0.),
                     method="DOP853",rtol=2e-12,atol=2e-14,dense_output=True)
    assert flat.success
    profiles={1.:profile}
    def bands(tidal, time):
        if tidal:
            amplitude=float(tidal)
            if amplitude not in profiles:
                def rhs(x,y):
                    a,b,da,db=y
                    return [da,db,4*amplitude*a/(9*x*x)-2*q*q*b*b*a,
                            -2*amplitude*b/(9*x*x)-q*q*(a*a+b*b)*b]
                solution=solve_ivp(rhs,(1.,10**-1.5-.001),(1.,1.,0.,0.),method="DOP853",
                                   rtol=2e-12,atol=2e-14,dense_output=True)
                assert solution.success
                profiles[amplitude]=solution.sol
            a,b = profiles[amplitude](1.-np.asarray(time))[:2]
        else:
            a = b = flat.sol(time)[0]
        # The two extremal spin-colour eigenvalues coincide and the two
        # central eigenlines have time-independent eigenvectors at rank two.
        return np.array([a/2,-a/2+b,-a/2-b])
    crossing = brentq(lambda t: bands(True,t)[1],0.,.95)
    return bands, crossing, 1.-10**-1.5


def continuum(bands, q, delta, time, tidal, order, steps, beta=None):
    """Unitary two-level evolution and exact endpoint expression for the current."""
    nodes, weights = roots_legendre(order)
    angles = (nodes+1)*np.pi/4
    momenta = delta*np.tan(angles)
    transverse = np.hypot(momenta,delta)[None,:]
    initial_mass = bands(tidal,0.)[:,None]
    energy = np.hypot(transverse,initial_mass)
    length = 1 if beta is None else np.tanh(beta*energy/2)
    sx,sz = -length*transverse/energy, -length*initial_mass/energy
    sy = np.zeros_like(sz)
    initial_sz = sz.copy()
    dt = time/steps
    for m in bands(tidal,(np.arange(steps)+.5)*dt).T:
        mass = m[:,None]
        energy = np.hypot(transverse,mass)
        nx,nz = transverse/energy,mass/energy
        cosine,sine = np.cos(2*q*energy*dt),np.sin(2*q*energy*dt)
        projection = (1-cosine)*(nx*sx+nz*sz)
        sx,sy,sz = (cosine*sx-sine*nz*sy+nx*projection,
                    cosine*sy+sine*(nz*sx-nx*sz),
                    cosine*sz+sine*nx*sy+nz*projection)
    np.testing.assert_allclose(sx*sx+sy*sy+sz*sz,np.broadcast_to(length**2,sz.shape),
                               rtol=0,atol=4e-12)
    charges = -(sz-initial_sz)@weights/8
    adiabatic = (np.arctan(bands(tidal,time)/delta)-np.arctan(bands(tidal,0.)/delta))/(2*np.pi)
    return charges, adiabatic


def signed_current_test(bands,q,delta,time):
    # Evolve both physical momenta and integrate the actual velocity vertex,
    # independently of the endpoint formula and the rotated Bloch propagator.
    p = .73
    transverse = np.hypot(p,delta)
    currents,changes = [],[]
    for signed in (p,-p):
        def rhs(t,wave):
            h = signed*SX+delta*SY+bands(True,t)[1]*SZ
            state = wave[:2]
            return np.r_[-1j*q*h@state,q*np.vdot(state,SX@state).real]
        initial = eigh(signed*SX+delta*SY+bands(True,0.)[1]*SZ)[1][:,0]
        sol = solve_ivp(rhs,(0.,time),np.r_[initial,0.],method="DOP853",rtol=4e-12,atol=1e-13)
        assert sol.success
        evolved = sol.y[:2,-1]
        currents.append(sol.y[2,-1].real)
        changes.append(np.vdot(evolved,SZ@evolved).real-np.vdot(initial,SZ@initial).real)
    np.testing.assert_allclose(sum(currents),-delta*sum(changes)/(2*transverse**2),
                               rtol=0,atol=3e-12)
    return sum(currents)


def sweep_and_chirality():
    pairs = []
    for lam,eps,p,d in ((.4,.9,-.73,.2),(-1.3,.15,.67,1.2)):
        def h(momentum):
            return np.kron(momentum*SX+d*SY,I2)+np.kron(SZ,lam*SZ+eps*SX)
        reflection = np.kron(SY,SY)
        np.testing.assert_allclose(reflection@h(p)@reflection,h(-p))
        np.testing.assert_allclose(reflection@np.kron(SX,I2)@reflection,-np.kron(SX,I2))
    for gap in (.1,.35,1.,1.8):
        # Infinite sweep, |dm/dt|=1. Stable quadrature even for a small gap.
        integral = quad(lambda k: gap*(-np.expm1(-np.pi*(k*k+gap*gap)))/
                        (np.pi*(k*k+gap*gap)),0.,np.inf,epsabs=2e-13)[0]
        np.testing.assert_allclose(integral,erf(np.sqrt(np.pi)*gap)/2,rtol=0,atol=2e-13)
        pairs.append(dict(gap_over_sqrt_slope=gap,transferred=integral))
    return pairs


def response_to_shear(bands,q,horizon):
    """At isotropy the singlet and the trace of the triplet have no linear response."""
    background,_=continuum(bands,q,.25,horizon,False,224,900)
    derivatives=[]
    for scale in (.16,.08,.04,.02):
        plus,_=continuum(bands,q,.25,horizon,scale,224,900)
        minus,_=continuum(bands,q,.25,horizon,-scale,224,900)
        linear=(plus-minus)/(2*scale)
        quadratic=(plus+minus-2*background)/(2*scale**2)
        derivatives.append(dict(scale=scale,triplet_m0_linear=linear[1],
                                total_linear=MULTIPLICITY@linear,
                                total_quadratic=MULTIPLICITY@quadratic))
    assert abs(derivatives[-1]["total_linear"])<abs(derivatives[0]["total_linear"])/50
    assert abs(derivatives[-1]["triplet_m0_linear"])>1e-4
    return derivatives


def interval_matrices(sites, spacing, delta):
    # Wilson term lifts the extra Dirac cone. The current below is evaluated
    # on the physical central bond, with open, charge-conserving ends.
    diagonal = np.kron(np.eye(sites),delta*SY+SZ/spacing)
    upper = np.diag(np.ones(sites-1),1)
    hopping = -(SZ+1j*SX)/(2*spacing)
    right = np.kron(upper,hopping)
    return diagonal+right+right.conj().T,hopping.conj().T


def compact_band(matrix):
    size = len(matrix)
    out = np.zeros((7,size),dtype=complex)
    for offset in range(-3,4):
        start,stop = max(0,offset),min(size,size+offset)
        out[3-offset,start:stop] = np.diag(matrix,k=offset)
    return out


def number_distribution(vectors, first_right):
    prob = np.array([1.])
    restricted = vectors[first_right:]
    eigenvalues = np.linalg.eigvalsh(restricted@restricted.conj().T)
    assert eigenvalues.min()>-3e-12 and eigenvalues.max()<1+3e-12
    for eigenvalue in np.clip(eigenvalues,0,1):
        prob = np.convolve(prob,[1-eigenvalue,eigenvalue])
    return prob


def edge_readout(matrix,spin_mass,mass,occupied,spacing,delta,actual_mass=None):
    """Simultaneous particle and hole occupations in the exact frozen eigenbasis."""
    sites=len(spin_mass)//2
    h=matrix+np.diag(mass*spin_mass)
    energy,vectors=eigh(h,check_finite=False)
    neg,pos=sites-1,sites
    end=vectors[:,[neg,pos]]
    overlap=end.conj().T@occupied
    density=overlap@overlap.conj().T
    hole=1-density[0,0].real
    particle=density[1,1].real
    joint=hole*particle+abs(density[0,1])**2
    np.testing.assert_allclose(energy[pos],-energy[neg],atol=4e-13)
    right=end[sites:]
    row=dict(negative_energy=energy[neg],positive_energy=energy[pos],
             particle_probability=particle,hole_probability=hole,compensated_pair_probability=joint,
             positive_in_right=np.linalg.norm(right[:,1])**2,
             negative_in_left=np.linalg.norm(end[:sites,0])**2)
    if actual_mass is not None:
        actual_h=matrix+np.diag(actual_mass*spin_mass)
        action=actual_h@end[:,1]
        row["positive_projector_commutator_norm"]=np.linalg.norm(
            action-end[:,1]*np.vdot(end[:,1],action))
    decay=1+spacing*mass
    if abs(decay)<1-1e-10:
        envelope=decay**np.arange(sites)
        norm=np.linalg.norm(envelope)
        left_state=np.kron(envelope/norm,np.array([1.,-1j])/np.sqrt(2))
        expected=abs(decay)**sites/(spacing*norm)
        residual=np.linalg.norm(h@left_state+delta*left_state)
        np.testing.assert_allclose(residual,expected,rtol=1e-8,atol=4e-13)
        row.update(decay_per_site=decay,left_trial_residual=residual,
                   left_trial_fidelity=abs(np.vdot(left_state,end[:,0]))**2)
    return row


def open_interval(bands,q,delta,sites,spacing,steps,times):
    matrix,bond = interval_matrices(sites,spacing,delta)
    spin_mass = np.tile(np.array([1.,-1.]),sites)
    times = np.array(times)
    first_right = sites  # two spinor components per site
    identity = np.eye(2*sites)
    runs = {}
    for tidal in (False,True):
        distributions = [np.array([1.]) for t in times]
        directional=[]
        edges=[]
        fixed_reader=[]
        sharp_cost=np.zeros(len(times))
        currents = np.zeros(len(times))
        ground = np.array([1.])
        for band,multiplicity in enumerate(MULTIPLICITY.astype(int)):
            initial_h = matrix+np.diag(bands(tidal,0.)[band]*spin_mass)
            energy,eigenvectors = eigh(initial_h,check_finite=False)
            v = eigenvectors[:,energy<0].copy()
            assert v.shape[1]==sites
            initial_count = np.linalg.norm(v[first_right:])**2
            ground_one = number_distribution(v,first_right)
            for copy in range(multiplicity):
                ground=np.convolve(ground,ground_one)
            previous=0.
            flux=0.
            for sample,end in enumerate(times):
                count=max(1,int(np.ceil(steps*(end-previous)/times[-1])))
                dt=(end-previous)/count
                masses=bands(tidal,previous+(np.arange(count)+.5)*dt)[band]
                constant=compact_band(identity+.5j*q*dt*matrix)
                for mass in masses:
                    lhs=constant.copy()
                    lhs[3]+=.5j*q*dt*mass*spin_mass
                    # The average of consecutive iterates solves lhs * average = v.
                    mid=solve_banded((3,3),lhs,v,check_finite=False)
                    left=mid[first_right-2:first_right]
                    right=mid[first_right:first_right+2]
                    flux+=2*q*dt*np.vdot(right,bond@left).imag
                    v=2*mid-v
                revised=np.linalg.norm(v[first_right:])**2
                np.testing.assert_allclose(revised-initial_count,flux,rtol=0,atol=2e-11)
                np.testing.assert_allclose(v.conj().T@v,np.eye(sites),atol=7e-12,rtol=0)
                distribution=number_distribution(v,first_right)
                bond_coherence=np.vdot(v[first_right:first_right+2],bond@v[first_right-2:first_right])
                sharp_cost[sample]-=2*multiplicity*bond_coherence.real
                if band==1:
                    directional.append(distribution)
                    edges.append(edge_readout(matrix,spin_mass,bands(tidal,end)[band],v,spacing,delta))
                    fixed_reader.append(edge_readout(matrix,spin_mass,bands(True,end)[band],v,spacing,delta,
                                                     actual_mass=bands(tidal,end)[band]))
                for copy in range(multiplicity):
                    distributions[sample]=np.convolve(distributions[sample],distribution)
                currents[sample]+=multiplicity*flux
                previous=end
        runs[tidal] = (np.array(distributions),currents,ground,directional,edges,sharp_cost,fixed_reader)
    output=[]
    for it,t in enumerate(times):
        baseline,falling = runs[False][0][it],runs[True][0][it]
        middle=2*sites
        ground=runs[True][2]
        cuts=np.arange(1,sites)
        electric_norm=spacing/2*np.sum((4*np.minimum(cuts,sites-cuts))**2)
        integers=np.arange(len(ground))
        np.testing.assert_allclose((falling-ground)@integers,runs[True][1][it],atol=1e-10)
        def discrimination(p1,p2):
            loss=np.sum((np.sqrt(p1)-np.sqrt(p2))**2)/2
            log_overlap=np.log1p(-loss)
            limit=.01
            necessary=int(np.ceil(np.log(4*limit*(1-limit))/(2*log_overlap)))
            sufficient=int(np.ceil(np.log(2*limit)/log_overlap))
            return dict(distance=np.abs(p1-p2).sum()/2,one_minus_overlap=loss,
                        copies_necessary_99=necessary,copies_sufficient_99=sufficient)
        output.append(dict(time=t,tidal_current=runs[True][1][it],flat_current=runs[False][1][it],
                           final_count_distance=np.abs(falling-baseline).sum()/2,
                           common_integer=middle,tidal_probability=falling[middle],
                           flat_probability=baseline[middle],
                           tidal_mean=falling@integers,flat_mean=baseline@integers,
                           tidal_sharp_charge_cost=runs[True][5][it],
                           flat_sharp_charge_cost=runs[False][5][it],
                           tidal_central_band=runs[True][4][it],flat_central_band=runs[False][4][it],
                           same_reader_on_flat=runs[False][6][it],
                           frozen_tidal_commutator=runs[True][6][it]["positive_projector_commutator_norm"],
                           electric_probability_error_per_coupling=q*t*electric_norm,
                           total_meter=discrimination(falling,baseline),
                           directional_meter=discrimination(runs[True][3][it],runs[False][3][it])))
    return output


def radiation_and_code():
    planck_mass=np.sqrt(hbar*c/G)
    solar_time=4.925490947e-6
    grain_mass=4*np.pi*(5e-5)**3*2500/3
    omega_min=.1
    result={}
    for name,mass in (("grain",grain_mass),("human",70.)):
        n=.0104/omega_min*(mass/planck_mass)**2
        result[name]=dict(mass_kg=mass,band_number_ceiling=n,
                          chance_of_nonvacuum_ceiling=min(1.,n),
                          discrimination_ceiling=(1+min(1.,np.sqrt(n)))/2)
    result.update(planck_mass_kg=planck_mass,ten_solar_frequency_hz=omega_min/(2*np.pi*10*solar_time),
                  one_quantum_necessary_mass_kg=planck_mass*np.sqrt(omega_min/.0104))
    # A guiding-centre code on the first torus with two units of flux.
    z=np.diag([1.,-1.])
    for trial in (SX,SY,SZ,I2,SX+2j*SZ):
        averaged=sum(u@trial@u.conj().T for u in (I2,SX,z,SX@z))/4
        np.testing.assert_allclose(averaged,np.trace(trial)*I2/2)
    result["first_compact_density_form_factor_squared_n2"]=np.exp(-np.pi/2)
    return result


def common_meter(bands,q,cross,dates,sites=128,spacing=.075,delta=.25):
    # Squaring the uniform Wilson chain in the sigma_y basis leaves a
    # bidiagonal matrix times its adjoint. Use its smallest singular value.
    def line(mass):
        central=mass+1/spacing
        diag=np.full(sites,central**2+spacing**-2)
        diag[0]=central**2
        off=np.full(sites-1,-central/spacing)
        lowest=eigh_tridiagonal(diag,off,eigvals_only=True,select="i",select_range=(0,0))[0]
        return 2*np.sqrt(lowest+delta**2)
    def changes(t):
        physical=bands(True,t)[1]
        flat=bands(False,t)[1]
        return abs(line(physical)-line(flat)),abs(physical-flat)
    nodes,weights=roots_legendre(40)
    def phase(a,b):
        values=np.array([changes(t) for t in (a+b)/2+(b-a)*nodes/2])
        return q*(b-a)/2*(weights@values)
    output=[]
    for end in dates:
        line_phase,recent=phase(cross,end)
        total=phase(0.,end)[1]
        reference=phase(0.,cross)[1]+recent
        np.testing.assert_allclose(total,reference,atol=2e-11,rtol=0)
        output.append(dict(time=end,line_phase_width=line_phase,
                           phase_only_success_ceiling=(1+np.sin(line_phase/2))/2,
                           one_particle_trace_distance_bound=total,
                           mass_integral_after_crossing=recent))
    return output


def calculate():
    q=.3
    bands,cross,horizon=prepare(q)
    before_horizon=1.-(1.5/10)**1.5
    rows=[]
    for d in (.05,.25,1.):
        for end in (cross,horizon):
            a,adiabatic=continuum(bands,q,d,end,True,448,1500)
            b,_=continuum(bands,q,d,end,True,256,750)
            background,_=continuum(bands,q,d,end,False,448,1500)
            hot,_=continuum(bands,q,d,end,True,448,1500,beta=1.)
            rows.append(dict(gap=d,time=end,one_per_band=a.tolist(),total=MULTIPLICITY@a,
                             flat=MULTIPLICITY@background,adiabatic=MULTIPLICITY@adiabatic,
                             thermal=MULTIPLICITY@hot,refinement=np.max(np.abs(a-b))))
    finite=[]
    for sites,spacing,steps in ((32,.1,260),(48,.075,360),(64,.05,480),(96,.1,360),
                                (128,.075,440),(128,.075,880)):
        finite.append(dict(sites=sites,spacing=spacing,steps=steps,
                           results=open_interval(bands,q,.25,sites,spacing,steps,[cross,before_horizon,horizon])))
    horizon_mass=bands(True,horizon)[1]
    return dict(q=q,crossing=cross,horizon=horizon,gap_time_product=q*(horizon-cross),
                signed_mass_at_horizon=horizon_mass,
                postcross_localization_weight=-np.expm1(-2*abs(horizon_mass)*q*(horizon-cross)),
                continuum=rows,interval=finite,sweep=sweep_and_chirality(),
                shear=response_to_shear(bands,q,horizon),
                deadline=common_meter(bands,q,cross,[before_horizon,horizon]),
                two_momentum_current=signed_current_test(bands,q,.25,horizon),
                radiation=radiation_and_code())


if __name__=="__main__":
    result=calculate()
    destination=Path(__file__).resolve().parents[1]/"verification"/"cat-tidal-current-results.json"
    destination.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
