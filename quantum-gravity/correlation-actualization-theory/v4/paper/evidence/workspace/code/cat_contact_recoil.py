"""Quantum normal motion at a matrix charge contact and orbital records of two cores.

The contact uses a scale-free variational boundary condition. It is a candidate
realization of the CAT port. The tidal orbit computation uses the original
linearized matrix propagation and adds no boundary condition at the core.
"""
import json
import os
from pathlib import Path

if __name__ == "__main__":
    for variable in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
        os.environ[variable] = "1"

import numpy as np
from scipy import linalg
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.sparse import diags, eye, kron
from scipy.special import roots_legendre

from cat_compensated_yukawa import prepare, geometry
from cat_core_multiplet import matched_caps, polarized_transfer
from cat_helicity_memory import Receiver, collective_masses, ordinary_sea, propagate, vacuum_profile
from cat_singular_clock import transfer, relative_vacuum_probability
from cat_timelike_receiver import radius

ROOT = Path(__file__).resolve().parents[1]


def spectrum_at_contact(cutoff):
    config = prepare(8, 1.95)
    start, g2 = 1.15, .16
    receiver = Receiver(config, cutoff, -1, start)
    old, _, (pos, vel, psi) = propagate(
        receiver, receiver.initial(), start, config.wall + .15, g2,
        recoil=True, return_contact=True)
    mass = collective_masses(config, g2)
    normal = np.array([config.j, 0, -1, 0, 1, 0, 0, 0])
    mu = 1 / np.sum(normal**2 / mass)
    direction = mu * normal / mass
    np.testing.assert_allclose([mu, normal @ pos, normal @ direction],
                               [(config.j+1)/(g2*(config.j+2)), 0, 1], atol=2e-10)
    kinetic = mu * (normal @ vel)**2 / 2
    tangential = vel - direction * (normal @ vel)
    np.testing.assert_allclose((mass @ vel**2)/2, kinetic+(mass @ tangential**2)/2)
    omega_sq, z, x = geometry(config, pos)
    n = 2*config.j+1
    h = (g2/n*receiver.quartic + np.sqrt(g2/(n*receiver.frequency))*receiver.hop
         + (omega_sq-receiver.frequency**2)*receiver.radii
         + diags(receiver.harmonic + z @ receiver.z)
         + x[0]*receiver.x[0]+x[1]*receiver.x[1]).toarray()
    def normal_hamiltonian(s):
        displaced = pos-direction*s
        om_new, z_new, x_new = geometry(config, displaced)
        membrane = mass[0]/2*sum(displaced[:2]**4-pos[:2]**4)
        change = ((om_new-omega_sq)*receiver.radii + diags(membrane+(z_new-z)@receiver.z)
                  + (x_new[0]-x[0])*receiver.x[0]+(x_new[1]-x[1])*receiver.x[1])
        return h+change.toarray()
    levels, basis = linalg.eigh(h)
    flux = basis.conj().T @ (psi / np.linalg.norm(psi))
    projectors = []
    for i, ell in enumerate(receiver.active):
        if abs(ell)+abs(receiver.dark) != 1:
            continue
        left = vacuum_profile(ell, receiver.frequency, np.sqrt(omega_sq), cutoff)
        right = vacuum_profile(receiver.dark, receiver.frequency, np.sqrt(omega_sq), cutoff)
        vector = np.zeros(receiver.shape)
        vector[i] = np.outer(left, right)
        projectors.append(vector.ravel()/np.linalg.norm(vector))
    reading = basis.conj().T @ np.column_stack(projectors)
    np.testing.assert_allclose(reading.conj().T @ reading, np.eye(len(projectors)), atol=1e-13)
    np.testing.assert_allclose(np.linalg.norm(reading.conj().T @ flux)**2,
                               old["probability_one"], atol=2e-12)
    return dict(levels=levels, basis=basis, flux=flux, reading=reading, mu=mu,
                kinetic=kinetic, momentum=abs(mu*(normal@vel)), crossing=old["time"],
                bare=old["probability_one"], bare_work=old["energy_change_for_sharp_one_or_other"],
                labels=np.repeat(receiver.charges, (cutoff+1)**2),
                normal_hamiltonian=normal_hamiltonian, gap=abs(x[0]), slope=normal@vel)


def momenta(levels, energy, mu):
    return np.sqrt(2*mu*(energy-levels)+0j)


def binary_wall(k, incident, port):
    """Solve only a rank(P)-dimensional system, including decaying channels."""
    # incident contains amplitudes, not flux-normalized coefficients.
    adjoint = port.conj().T
    direct = adjoint @ (k[:, None]*port)
    inverse = adjoint @ (port / k[:, None])
    incoming = adjoint @ incident
    incoming_derivative = adjoint @ (k*incident)
    selected = linalg.solve(np.eye(port.shape[1])+3*inverse@direct,
                            2*(incoming+inverse@incoming_derivative))
    reflected = (port @ (incoming_derivative-1.5*direct@selected))/k + .5*port@selected
    written = port@selected
    return [reflected, written, incident+reflected-written]


def multi_wall(k, incident, basis, labels):
    """Independent dense matching at the wall, diagonal in the actual charge basis."""
    wave_operator = (basis * k) @ basis.conj().T
    blocks = wave_operator * (labels[:, None] == labels)
    trace = linalg.solve(wave_operator+blocks, 2*basis@(k*incident))
    return [basis.conj().T@trace-incident] + [
        basis.conj().T@(trace*(labels == label)) for label in np.unique(labels)]


def observables(levels, energy, k, incident, outgoing):
    weight = k.real
    incoming_spectrum = weight*abs(incident)**2
    outputs = [weight*abs(vector)**2 for vector in outgoing]
    delta = sum(outputs)-incoming_spectrum
    mass_balance = delta.sum()
    assert abs(mass_balance) < 3e-10 * max(1., incoming_spectrum.sum())
    change, work = delta@levels, delta@(energy-levels)
    assert abs(change+work) < 5e-9 * max(1., abs(energy)*incoming_spectrum.sum())
    return np.array([incoming_spectrum.sum(), *[row.sum() for row in outputs], change, work])


def shell_sample(material, scale=1., charges=False):
    levels, basis, flux = (material[key] for key in ("levels", "basis", "flux"))
    energy = abs(flux)**2 @ levels + scale*material["kinetic"]
    k = momenta(levels, energy, material["mu"])
    mask = k.real > 0
    weight = np.sum(abs(flux[mask])**2)
    incident = np.zeros_like(flux)
    incident[mask] = flux[mask]/np.sqrt(weight*k[mask].real)
    if charges:
        outgoing = multi_wall(k, incident, basis, material["labels"])
    else:
        outgoing = binary_wall(k, incident, material["reading"])
    result = observables(levels, energy, k, incident, outgoing)
    return dict(kinetic_scale=scale, total_energy=energy, omitted_flux_weight=max(0., 1-weight),
                open=int(mask.sum()), reflection=result[1], transmitted=result[2:-2].tolist(),
                internal_energy_change=result[-2], kinetic_energy_change=result[-1])


def resolved_wall(material, cells, width_factor):
    """Restore the ordinary potentials along the physical normal on each lead.

    At the cuts use the local constant continuation, with incoming flux chosen
    to reproduce the same unbranched boundary value for every comparison.
    """
    hamiltonian = material["normal_hamiltonian"]
    mu = material["mu"]
    energy = abs(material["flux"])**2@material["levels"]+material["kinetic"]
    kref = material["momentum"]
    length = material["gap"]*width_factor
    kz = momenta(material["levels"],energy,mu).real
    center = material["basis"]@(material["flux"]/np.sqrt(kz))
    def normal_modes(s):
        levels, basis = linalg.eigh(hamiltonian(s))
        assert energy > levels[-1]
        return np.sqrt(2*mu*(energy-levels)), basis

    def boundary(sign):
        edge = sign*length
        wave, basis = normal_modes(edge)
        amplitude = basis.copy()
        derivative = basis*(sign*wave/kref)
        # One column per outgoing channel. Negative step on the right lead.
        step = -edge/cells
        for i in range(cells):
            k, vectors = normal_modes(edge+(i+.5)*step)
            phase = k*step
            value = vectors.conj().T@amplitude
            slope = vectors.conj().T@derivative
            cosine = np.cos(phase)[:,None]
            sine = 1j*np.sin(phase)[:,None]
            amplitude = vectors@(cosine*value+(kref/k)[:,None]*sine*slope)
            derivative = vectors@((k/kref)[:,None]*sine*value+cosine*slope)
        admittance = linalg.solve(amplitude.T,derivative.T).T
        return wave, amplitude, admittance
    kl, left, yl = boundary(-1)
    kr, right, yr = boundary(1)
    # Propagate the ordinary unbranched solution back to the left cut and
    # decompose its value and spatial derivative into both traveling directions.
    positive_flux = lambda a, k: float(np.sum(k*abs(a)**2))
    kedge, edge_basis = normal_modes(-length)
    val, slope = center.copy(), yr@center
    step = -length/cells
    for i in range(cells):
        k, vec = normal_modes((i+.5)*step)
        value, deriv = vec.conj().T@val, vec.conj().T@slope
        cosine, sine = np.cos(k*step), 1j*np.sin(k*step)
        val = vec@(cosine*value+(kref/k)*sine*deriv)
        slope = vec@((k/kref)*sine*value+cosine*deriv)
    f = edge_basis.conj().T@val
    d = kref/kedge*(edge_basis.conj().T@slope)
    incident, reflected0 = (f+d)/2, (f-d)/2
    norm = positive_flux(incident,kl)
    bare = positive_flux(reflected0,kl)/norm
    direct = linalg.solve(right,center)
    assert abs(bare+positive_flux(direct,kr)/norm-1)<1e-10

    port = material["basis"]@material["reading"]
    py = port@(port.conj().T@yr)
    yp = (yr@port)@port.conj().T
    pinched = yr-py-yp+2*(py@port)@port.conj().T
    trace = linalg.solve(pinched-yl,(yr-yl)@center)
    reflected = reflected0+linalg.solve(left,trace-center)
    selected = port@(port.conj().T@trace)
    written, other = linalg.solve(right,np.column_stack([selected,trace-selected])).T
    values = np.array([positive_flux(reflected,kl),positive_flux(written,kr),
                       positive_flux(other,kr)])/norm
    assert abs(values.sum()-1)<2e-10
    in_levels, out_levels = energy-kl**2/(2*mu), energy-kr**2/(2*mu)
    change = ((kl*(abs(reflected)**2-abs(incident)**2))@in_levels +
              (kr*(abs(written)**2+abs(other)**2))@out_levels)/norm
    return dict(halfwidth=length,cells_per_side=cells,ordinary_reflection=bare,
                reflection=values[0],written=values[1],other=values[2],
                ordinary_plus_material_energy_change=change)


def ground_limit(material):
    levels = material["levels"]
    first = np.flatnonzero(levels-levels[0] > 1e-8)[0]
    assert first == 1
    signal = np.linalg.norm(material["reading"][0])**2
    assert 1e-10 < signal < 1-1e-10
    rows = []
    for fraction in (.01, .001, .0001, .00001):
        energy = levels[0]+(levels[first]-levels[0])*fraction
        k = momenta(levels, energy, material["mu"])
        incident = np.zeros_like(k)
        incident[0] = 1/np.sqrt(k[0])
        out = binary_wall(k, incident, material["reading"])
        values = observables(levels, energy, k, incident, out)
        rows.append(dict(gap_fraction=fraction, reflection=values[1], written=values[2],
                         transmission=values[2]+values[3]))
    return dict(ground_bare=signal, rows=rows)


def wave_packet(material, width_factor, spectral_order, with_window=False):
    """An uncorrelated incoming positive-momentum packet at the free reference plane."""
    levels, flux, mu = (material[key] for key in ("levels", "flux", "mu"))
    position_width = width_factor*material["gap"]
    halfwidth = np.pi/(np.sqrt(3)*position_width)
    p0 = material["momentum"]
    assert p0 > halfwidth
    lower = levels.min()+(p0-halfwidth)**2/(2*mu)
    upper = levels.max()+(p0+halfwidth)**2/(2*mu)
    nodes, weights = roots_legendre(spectral_order)
    energies = (upper+lower)/2+(upper-lower)*nodes/2
    weights *= (upper-lower)/2
    integrated = np.zeros(6)
    fields, slopes = [], []
    for energy, weight in zip(energies, weights):
        k = momenta(levels, energy, mu)
        incident = np.zeros_like(k)
        use = (k.real > 0) & (abs(k.real-p0) < halfwidth)
        shape = 2/np.sqrt(3*halfwidth)*np.cos(np.pi*(k[use].real-p0)/(2*halfwidth))**2
        incident[use] = np.sqrt(mu)*flux[use]*shape/k[use]
        reflected, wrote, other = binary_wall(k, incident, material["reading"])
        integrated += weight*observables(levels, energy, k, incident, [reflected,wrote,other])
        if with_window:
            # All derivatives are outward. The true spatial derivative is i times slope.
            fields.append([incident+reflected, wrote, other])
            slopes.append([k*(reflected-incident), k*wrote, k*other])
    assert abs(integrated[0]-1)<2e-7
    result = dict(spatial_width=position_width, momentum_halfwidth=halfwidth,
                  normalization=integrated[0], reflection=integrated[1], written=integrated[2],
                  internal_work=integrated[-2], normal_work=integrated[-1])
    if with_window:
        selected = np.asarray(fields)[:,1,:]
        fields = np.asarray(fields).reshape(len(energies), -1)
        slopes = np.asarray(slopes).reshape(len(energies), -1)
        unit = position_width/abs(material["slope"])
        windows = []
        times, time_weights = roots_legendre(64)
        for scale in (1., 2., 4., 8.):
            half_duration = scale*unit
            # Subtract a carrier energy only in the common phase, not in the energy current.
            fourier = np.exp(-1j*np.outer(times*half_duration, energies-energies.mean()))*weights
            value = (fourier@fields).reshape(len(times),3,-1)
            derivative = (fourier@slopes).reshape(value.shape)
            energy_value = ((fourier*energies)@fields).reshape(value.shape)
            currents = (value.conj()*derivative).sum(axis=2).real/(2*np.pi)
            energy_currents = (energy_value.conj()*derivative).sum(axis=2).real/(2*np.pi)
            assert np.max(abs(currents.sum(axis=1)))<2e-9
            assert np.max(abs(energy_currents.sum(axis=1)))<9e-7
            net = (half_duration*time_weights)@currents
            energy_net = (half_duration*time_weights)@energy_currents
            windows.append(dict(half_duration=half_duration, write_flux=net[1],
                                energy_on_written_port=energy_net[1],
                                share_of_asymptotic_write=net[1]/result["written"],
                                probability_current_residual=max(abs(currents.sum(axis=1))),
                                energy_current_residual=max(abs(energy_currents.sum(axis=1)))))
        result["windows"] = windows
        # Finite-time selection of the spatial output differs from its conserved
        # asymptotic label. Resolve the kinetic cost of a continuous two-outcome
        # reading on the selected physical lead. The temporal origin is the
        # free packet's crest at the crossing.
        k_grid = np.sqrt(2*mu*(energies[:,None]-levels)+0j)
        spatial_nodes, spatial_weights = roots_legendre(32)
        smoothing = []
        for clock in (0., 2*unit, 4*unit):
            amplitudes = (weights*np.exp(-1j*(energies-energies.mean())*clock))[:,None]*selected
            def density(distance):
                wave = (amplitudes*np.exp(1j*k_grid*distance)).sum(axis=0)
                return mu*np.vdot(wave,wave).real/(2*np.pi)
            for length in (position_width, position_width/2, position_width/4):
                densities = np.array([density(length*(t+1)/2) for t in spatial_nodes])
                integral = length*spatial_weights@densities/2
                inverse_integral = length*spatial_weights@(1/densities)/2
                optimum = np.pi**2/(8*mu*inverse_integral)
                uniform = (np.pi/(2*length))**2*integral/(2*mu)
                assert 0 < optimum <= uniform*(1+1e-13)
                smoothing.append(dict(clock=clock,length=length,density_at_contact=density(0),
                                      minimum_work=optimum,linear_angle_work=uniform))
        result["local_read_cost"] = smoothing
    return result


def local_threshold_control():
    # Two exact coupled internal energies, independent of the matrix truncation.
    # The rotation below diagonalizes H in the charge basis.
    angle = .57
    basis = np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])
    port = basis[:1].T
    levels = np.array([.2, 1.7])
    for energy in (.20003, 1.69, 1.71, 6., 400.):
        k = momenta(levels, energy, .8)
        open_channels = np.flatnonzero(k.real > 0)
        columns = []
        for n in open_channels:
            incoming = np.zeros(2, complex)
            incoming[n] = 1/np.sqrt(k[n])
            lowrank = binary_wall(k, incoming, port)
            dense = multi_wall(k, incoming, basis, np.arange(2))
            np.testing.assert_allclose(lowrank, dense, atol=2e-12)
            columns.append(np.concatenate([np.sqrt(k.real)*v for v in dense]))
        matrix = np.column_stack(columns)
        np.testing.assert_allclose(matrix.conj().T @ matrix, np.eye(len(columns)), atol=3e-12)
    # Above every threshold the high-energy reflection coefficient is the
    # off-block part of H, divided by -4E, in the incoming material basis.
    physical_h = (basis*levels)@basis.T
    off = physical_h-np.diag(physical_h.diagonal())
    energy = 1e5
    k = momenta(levels, energy, 1.)
    reflection = np.column_stack([multi_wall(k, v, basis, np.arange(2))[0] for v in np.eye(2)])
    np.testing.assert_allclose(4*energy*basis@reflection@basis.T, -off, atol=2e-5)


def neutral_receiver(cutoff, helicity):
    """Use the full half-filled receiver, with both Fermi banks and two quartic modes."""
    config = prepare(8, 1.95)
    g2 = .16
    earlier, (left,right,pos,vel,psi) = ordinary_sea(
        config,1.15,g2,cutoff,helicity,recoil=True,return_contact=True)
    psi /= np.linalg.norm(psi)
    om2,z,x = geometry(config,pos)
    hl, hr = [bank.operators(om2,z,x) for bank in (left,right)]
    unit = eye(hl.shape[0],format="csr")
    h = (kron(hl,unit)+kron(unit,hr)
         - 2*g2/(2*config.j+1)*kron(left.radius,right.radius)).tocsr()
    ref = np.vdot(psi,h@psi).real
    mu = (config.j+1)/(g2*(config.j+2))
    kinetic = mu*(config.j*vel[0]+vel[4]-vel[2])**2/2
    bounded = (h-diags(np.full(h.shape[0],ref)))/kinetic
    eta = float(np.max(np.asarray(abs(bounded).sum(axis=1))))
    assert eta < .5
    order = 1
    while eta**(order+1)/(1-eta) > 2e-14:
        order += 1
    def power(vector, exponent):
        coefficients = [1.]
        for i in range(1,order+1):
            coefficients.append(coefficients[-1]*(i-1-exponent)/i)
        total = coefficients[-1]*vector
        for coefficient in coefficients[-2::-1]:
            total = bounded@total+coefficient*vector
        return total
    # Compact positive half powers are evaluated on every populated charge,
    # never by discarding high internal eigenchannels.
    def wave(vector):
        return power(vector,.5)
    labels = np.add.outer(np.repeat(left.charges,cutoff+1),
                          np.repeat(right.charges,cutoff+1)).ravel()
    first, second = np.meshgrid(np.arange(len(left.angular)),np.arange(len(right.angular)),
                                 indexing="ij")
    use = abs(left.angular[first])+abs(right.angular[second])==1
    radii = []
    for bank in (left,right):
        profiles = np.array([vacuum_profile(a,bank.frequency,np.sqrt(om2),cutoff) for a in bank.angular])
        profiles /= np.linalg.norm(profiles,axis=1)[:,None]
        radii.append(profiles)
    tensor_shape = (*left.shape,*right.shape)
    def one(vector, sign):
        grid = vector.reshape(tensor_shape)
        overlap = np.einsum("irjs,ir,js->ij",grid,*radii)
        accept = use & ((left.charges[:,None]+right.charges)==sign)
        return ((overlap*accept)[:,None,:,None]*radii[0][:,:,None,None]
                *radii[1][None,None,:,:]).ravel()
    def reading(vector, full):
        if full:
            return [np.where(labels==q,vector,0) for q in range(-4,5)]
        plus, minus = one(vector,1),one(vector,-1)
        return [minus, plus, vector - minus - plus]
    incident = power(psi,-.25)
    rhs = 2*wave(incident)
    output = []
    for full in (False,True):
        def match(trace):
            filtered = [reading(wave(v),full)[i] for i,v in enumerate(reading(trace,full))]
            return wave(trace)+sum(filtered)
        trace = incident.copy()
        for iteration in range(45):
            residual = rhs-match(trace)
            if np.linalg.norm(residual)<2e-12:
                break
            trace += residual/2
        else:
            raise ValueError("The variational matching failed to converge")
        channels = [power(v,.25) for v in [trace-incident,*reading(trace,full)]]
        probabilities = [float(np.vdot(v,v).real) for v in channels]
        assert abs(sum(probabilities)-1)<1e-10
        work = sum(np.vdot(v,h@v).real for v in channels)-ref
        recoil = sum(np.vdot(v,(ref+kinetic)*v-h@v).real for v in channels)-kinetic
        assert abs(work+recoil) < 1e-8
        output.append(dict(reflection=probabilities[0],outputs=probabilities[1:],
                           internal_work=work,normal_work=recoil,
                           residual=float(np.linalg.norm(residual))))
    if cutoff == 0:
        levels, basis = linalg.eigh(h.toarray())
        energies = ref+kinetic
        k = momenta(levels,energies,mu)
        inc = (basis.conj().T@psi)/np.sqrt(k)
        dense = multi_wall(k,inc,basis,labels)
        explicit = observables(levels,energies,k,inc,dense)
        np.testing.assert_allclose(explicit[1:-2],
                                   [output[1]["reflection"],*output[1]["outputs"]],atol=2e-12)
    return dict(cutoff=cutoff, helicity=helicity, dimension=h.shape[0], clock=earlier["clock"],
                kinetic=kinetic, operator_row_bound=eta, order=order,
                series_tail_bound=eta**(order+1)/(1-eta), bare_one=earlier["probability_one"],
                one_residual=output[0], all_charges=output[1])


def material_spin():
    g2 = .16
    config = prepare(8,1.95)
    def read(level):
        info, (left,right,pos,vel,psi)=ordinary_sea(
            config,1.15,g2,3,1,recoil=True,return_contact=True,crossing_level=level)
        psi = psi.reshape(left.initial.size,right.initial.size)
        norm = np.vdot(psi,psi).real
        prob = abs(psi)**2/norm
        q = (np.repeat(left.charges,left.shape[1])@prob.sum(axis=1)
             +np.repeat(right.charges,right.shape[1])@prob.sum(axis=0))
        spin_z = left.z[0]@prob.sum(axis=1)+right.z[0]@prob.sum(axis=0)
        spin_x = np.vdot(psi,left.x[0]@psi+(right.x[0]@psi.T).T).real/norm
        _,z,x = geometry(config,pos)
        gap = abs(x[0])
        slope = config.j*vel[0]+vel[4]-vel[2]
        expected = (4+q-(z[0]*spin_z+x[0]*spin_x)/np.hypot(z[0],x[0]))/2
        return dict(level=level,clock=info["clock"],gap=gap,slope=slope,
                    total_left=4+q,ordinary_lower_left=expected,spin_z=spin_z)
    center=read(0.)
    gap, slope = center["gap"], abs(center["slope"])
    mu = (config.j+1)/(g2*(config.j+2))
    windows = [read(ratio*gap) for ratio in (2.,1.,-1.,-2.)]
    # Validate the quantum metric directly from the finite-difference band projector.
    from cat_compensated_yukawa import SX, SZ
    for s in (-gap,0.,2*gap):
        def lower(t):
            return (np.eye(2)-(t*SZ+gap*SX)/np.hypot(t,gap))/2
        step=gap*1e-5
        derivative=(lower(s+step)-lower(s-step))/(2*step)
        np.testing.assert_allclose(np.trace(derivative@derivative).real/2,
                                   gap**2/(4*(s**2+gap**2)**2),rtol=3e-9)
    # The reference colour is contracted at a Yukawa vertex. Different holes
    # in a filled physical bank are orthogonal final occupation states.
    for count in range(1,6):
        transfer_colour = np.kron([[0.,1.],[0.,0.]],np.eye(count))
        generator = np.add.outer(np.arange(count),np.arange(count))
        gauge = np.kron(np.eye(2),generator)
        np.testing.assert_allclose(gauge@transfer_colour,transfer_colour@gauge)
        occupied = sum(1<<(count+i) for i in range(count))
        amplitudes={}
        for i in range(count):
            removed = occupied ^ (1<<(count+i))
            parity = ((occupied & ((1<<(count+i))-1)).bit_count()
                      +(removed & ((1<<i)-1)).bit_count())
            target = removed | (1<<i)
            amplitudes[target]=amplitudes.get(target,0)+(-1)**parity
        assert sum(weight**2 for weight in amplitudes.values())==count
    families=[]
    for j in (8,32,128,512,2048):
        for fixed_k in (False,True):
            k = .45 if fixed_k else 1/np.sqrt(j*(j+1))
            m = np.hypot(.6,k)
            dw = radius(config.wall+k/2)-radius(config.wall-k/2)
            omega = np.sqrt(m*m+j*(j+1)*dw*dw)
            xi=(omega+m)/(2*(j+1))
            assert 0 < xi < m
            np.testing.assert_allclose(xi+np.hypot(j*dw,m-xi),omega,rtol=2e-15)
            spin_weight=j*dw**2/(4*xi*np.hypot(j*dw,m-xi))
            vertex_sq=g2*spin_weight/(2*(2*j+1)*omega)
            for count in (j+1,(j+1)**2):
                stack_mass=1/(g2*(1/(j+1)+1/count))
                families.append(dict(j=j,point_rank=count,k=k,frequency=omega,half_gap=xi,
                                     mass=stack_mass,localization_parameter=stack_mass*xi**3,
                                     single_link_resonant_vertex_squared=vertex_sq,
                                     filled_colour_short_time_coefficient=count*vertex_sq))
    return dict(center=center,windows=windows,mu=mu,geometric_peak=1/(8*mu*gap**2),
                localization_parameter=mu*gap**3,minimum_rms_adiabatic_ratio=1/(8*mu*gap**3),
                mean_speed_adiabatic_ratio=slope/(4*gap**2),
                infinite_linear_isolated_spin_flip=-np.expm1(-np.pi*gap**2/slope),
                resonant_stacks=families)


def relative_sphere_index(j, reference_spin):
    """All signed eigenvalues of the axial bifundamental Pauli operator."""
    modes = {}
    for left in range(-j,j+1):
        for right in range(-reference_spin,reference_spin+1):
            for spin in (-1,1):
                modes.setdefault(2*(left+right)+spin,[]).append((left,right,spin))
    def spectrum(displacement):
        parts = []
        for states in modes.values():
            indices = {state:i for i,state in enumerate(states)}
            block = np.zeros((len(states),len(states)))
            for i,(left,right,spin) in enumerate(states):
                block[i,i] = spin*(left-right-displacement)
                if spin == -1:
                    entries = [((left-1,right,1),np.sqrt((j+left)*(j-left+1))),
                               ((left,right-1,1),-np.sqrt((reference_spin+right)*(reference_spin-right+1)))]
                    for target,value in entries:
                        if target in indices:
                            block[indices[target],i] = block[i,indices[target]] = value
            parts.extend(linalg.eigvalsh(block))
        return np.sort(parts)
    contact = reference_spin-j
    vals = spectrum(contact)
    zeros = abs(vals)<1e-10
    shift = 1e-5
    jump = int(round(sum(np.sign(spectrum(contact+shift))-np.sign(spectrum(contact-shift)))/2))
    gap = min(abs(vals[~zeros]))
    if reference_spin == j:
        assert jump == 0 and zeros.sum()==4*j+2
    else:
        assert jump == 1 and zeros.sum()==1
        assert 2/(4*j-1)<gap<2/(4*j-2)
        np.testing.assert_allclose(gap**3-(4*j-1)*gap+2,0,atol=2e-11)
    return dict(j=j,reference_spin=reference_spin,index_jump=jump,zero_modes=int(zeros.sum()),
                nearest_other_in_units_of_radius=float(gap))


def finite_passage(j, corotating, tight=False, offset_fraction=0.):
    """First-order Yukawa capture using exact free spin and boson propagators.

    The reference sphere breathes with opposite signed radius on the same
    matrix clock. Its extremal fermion link uses the conjugate colour spin.
    """
    from cat_compensated_yukawa import SX, SY, SZ
    wall,k,m,g2 = 1.95,.45,.6,.16
    count = (j+1)**2
    gap = np.hypot(k,m)
    offset = 0.
    def geometry_at(t):
        wleft, wright = radius(t+k/2),radius(t-k/2)
        difference = wright-wleft
        coefficient = 1 if corotating else j
        left = coefficient*(wleft-radius(wall+k/2))-.4*(t-wall)+offset
        return left,left+j*difference,np.hypot(gap,np.sqrt(j*(j+1))*difference)
    omega = geometry_at(wall)[2]
    xi = (omega+gap)/(2*(j+1))
    enter = brentq(lambda t:geometry_at(t)[0]-xi,wall-.5,wall)
    leave = brentq(lambda t:geometry_at(t)[0]+xi,wall,wall+.5)
    # Resolve reference copies by their ordinary centre positions; use the
    # same physical preparation and comparison times for every displaced copy.
    offset = offset_fraction*xi
    contact = brentq(lambda t:geometry_at(t)[0],enter,leave)
    left0,right0,om0 = geometry_at(enter)
    # Left lower state already occupied. The empty and occupied spinors are
    # advanced by the ordinary time-dependent fermion equations on both ends.
    left_spin = linalg.eigh(left0*SZ+xi*SX)[1][:,1]
    right_spin = linalg.eigh(right0*SZ+(xi-gap)*SX)[1][:,0]
    oscillator = 1/np.sqrt(2*om0)
    initial = np.r_[left_spin,right_spin,oscillator,-1j*om0*oscillator,0j]
    def rhs(t,state):
        zl,zr,om = geometry_at(t)
        a,b,f,df = state[:2],state[2:4],state[4],state[5]
        return np.r_[-1j*(zl*SZ+xi*SX)@a,-1j*(zr*SZ+(xi-gap)*SX)@b,
                     df,-om**2*f,-1j*f*np.vdot(a,SY@b)]
    sol = solve_ivp(rhs,(enter,leave),initial,method="DOP853",
                    rtol=1e-11 if tight else 4e-9,atol=1e-13 if tight else 4e-11)
    assert sol.success
    state = sol.y[:,-1]
    np.testing.assert_allclose([np.vdot(state[:2],state[:2]).real,np.vdot(state[2:4],state[2:4]).real,
                                -2*np.imag(state[4].conjugate()*state[5])],1.,atol=2e-6)
    received = count*g2/(2*j+1)*abs(state[-1])**2
    return dict(j=j,reference_spin=j-1 if corotating else 0,reference_copies=count,
                beginning=enter,end=leave,duration=leave-enter,
                contact=contact,
                leading_received_weight=received,
                equal_reference_rank_weight=received if corotating else (2*j-1)*received)


def orbital_overlap(first, second):
    value = relative_vacuum_probability(first, second)
    # Check the overlap by integrating two Gaussian wave functions in position space.
    def width(matrix):
        aq, bp = matrix[:2,:2], matrix[:2,2:]
        cq, dp = matrix[2:,:2], matrix[2:,2:]
        return linalg.solve((aq+1j*bp).T, (cq+1j*dp).T).T
    a, b = width(first), width(second)
    check = (4*np.sqrt(linalg.det(a.imag)*linalg.det(b.imag)) /
             abs(linalg.det(b-a.conj())))
    np.testing.assert_allclose(check, value, rtol=2e-9)
    return value


def phases_and_tags():
    clock, coefficients, _, end = matched_caps()
    ks = [.16, .16+np.sqrt(2/1056)]
    chances = np.ones(2)
    phases = np.zeros(2)
    orbital = []
    for k in ks:
        maps = []
        for i, strength in enumerate((0., .08)):
            source = lambda u: coefficients(u, strength)[:3]
            m = transfer(clock, source, end, k)
            tight = transfer(clock, source, end, k, tight=True)
            np.testing.assert_allclose(m, tight, atol=3e-9, rtol=3e-9)
            maps.append(m)
            response = polarized_transfer(clock, coefficients, strength, k, direct=True)[4:6,:2]
            circular = response[0,0]-1j*response[1,0]
            chances[i] *= abs(circular)**2
            phases[i] += np.angle(circular)
        orbital.append(maps)
    weights = chances / chances.sum()
    delta = phases[1]-phases[0]

    def deficit(squared_overlap):
        d = 4*np.prod(weights)*squared_overlap*np.sin(delta)**2
        return d/(2*(1+np.sqrt(1-d)))

    # Identical Gaussian preparations for both cores, with variable squeezing
    # of both position quadratures and reciprocal momentum squeezing.
    rows = []
    for width in (.5, 1., 2.):
        squeeze = np.diag([width,width,1/width,1/width])
        outputs = [[m@squeeze for m in pair] for pair in orbital]
        squares = [orbital_overlap(*pair) for pair in outputs]
        # A concrete measurement on the first charge reads the outbound relative
        # Y coordinate. Other quadratures and the partner are discarded here.
        relative = np.array([1., -1., 0., 0.])
        variances = [np.linalg.norm(relative@m)**2/2 for m in outputs[0]]
        def read_quadrature(variances):
            variances = np.asarray(variances)
            def loss(x):
                a,b = weights*np.exp(-x*x/(2*variances))/np.sqrt(2*np.pi*variances)
                if a+b == 0:
                    return 0.
                d = 4*a*b*np.sin(delta)**2
                return d/(2*(a+b+np.sqrt(max(0., (a+b)**2-d))))
            # Split at the smaller width: a squeezed output can contain two very
            # different length scales. The omitted Gaussian tail is < 2e-44.
            scales = np.sqrt(variances)
            small, large = min(scales), max(scales)
            points = sorted({0., small/large, min(8*small/large, 14.), 14.})
            return 2*sum(quad(lambda t:large*loss(large*t), a, b, epsabs=1e-20,
                              epsrel=2e-11)[0] for a,b in zip(points,points[1:]))

        one_read = read_quadrature(variances)
        covariances = [m@m.T/2 for m in outputs[0]]
        def best_gradient(gradients):
            c0, c1 = [gradients@c@gradients.T for c in covariances]
            ratios, axes = linalg.eigh(c1, c0)
            options = []
            for i in (0, -1):
                axis = axes[:,i]/np.linalg.norm(axes[:,i])
                if axis[np.argmax(abs(axis))]<0:
                    axis = -axis
                v = [axis@c@axis for c in (c0,c1)]
                options.append((read_quadrature(v), v[1]/v[0], axis))
            best, ratio, axis = min(options, key=lambda item:item[0])
            return dict(ratio=ratio, deficit=best, gradient_coefficients=axis.tolist())
        fplus, fminus = [coefficients(clock(1.4)+sign*ks[0]/2,0.)[2] for sign in (1,-1)]
        gradients = np.array([[1.,-1.,0,0],[0,0,1.,1.],[fplus,-fminus,0,0],[0,0,fplus,fminus]])
        plain, all_axes = best_gradient(gradients[:2]), best_gradient(gradients)
        assert deficit(np.prod(squares)) <= deficit(squares[0])+1e-16
        assert deficit(squares[0]) <= one_read+1e-16 <= deficit(1.)+2e-16
        assert deficit(squares[0]) <= all_axes["deficit"]+1e-16 <= plain["deficit"]+2e-16
        rows.append(dict(initial_width=width, single_overlaps_squared=squares,
                         pair_overlap_squared=np.prod(squares), relative_y_variances=variances,
                         both_orbits_deficit=deficit(np.prod(squares)),
                         first_orbit_deficit=deficit(squares[0]), one_coordinate_deficit=one_read,
                         best_plain=plain, best_four_gradients=all_axes))
    return dict(ks=ks, both_arrive=chances.tolist(), posterior=weights.tolist(), phase_difference=delta,
                no_orbit_deficit=deficit(1.), gaussian_inputs=rows)


def main():
    local_threshold_control()
    materials = []
    for cutoff in (3, 5):
        material = spectrum_at_contact(cutoff)
        entry = {key:material[key] for key in
                 ("mu","kinetic","momentum","crossing","gap","slope","bare","bare_work")}
        entry.update(cutoff=cutoff, dimension=len(material["levels"]),
                     one_quantum=[shell_sample(material, scale) for scale in (.1, 1., 4.)],
                     signed_charges=shell_sample(material,charges=True), slow=ground_limit(material))
        packets = [wave_packet(material, w, 384, with_window=(w==1 and cutoff==5)) for w in (1, 2)]
        for index, w in enumerate((1,2)):
            check = wave_packet(material, w, 224)
            for name in ("normalization","written","internal_work"):
                assert abs(check[name]-packets[index][name]) < 3e-7
        entry["packets"]=packets
        materials.append(entry)
    profiles = []
    for cut, cells in ((2,6),(2,12),(2,24),(3,16)):
        profile = resolved_wall(spectrum_at_contact(cut),cells,1.)
        profile["cutoff"]=cut
        profiles.append(profile)
    assert abs(profiles[-1]["written"]-profiles[-2]["written"])<3e-7
    sea = [neutral_receiver(cut,helicity) for cut,helicity in ((2,1),(4,1),(4,-1))]
    neutral_receiver(0,1)
    for read in ("one_residual","all_charges"):
        np.testing.assert_allclose(sea[1][read]["outputs"],sea[2][read]["outputs"],atol=2e-11)
        np.testing.assert_allclose(sea[0][read]["outputs"],sea[1][read]["outputs"],atol=4e-7)
    passage = [finite_passage(j,comoving) for j in (8,32,128,512,2048) for comoving in (False,True)]
    for row in passage[-2:]:
        check=finite_passage(row["j"],row["reference_spin"]>0,tight=True)
        np.testing.assert_allclose(row["leading_received_weight"],check["leading_received_weight"],rtol=2e-6)
    indices=[relative_sphere_index(j,r) for j in (2,4,8,16,32) for r in (j-1,j)]
    separated=[finite_passage(8,True,offset_fraction=f) for f in np.linspace(-.1,.1,5)]
    times=[row["contact"] for row in separated]
    assert np.min(np.diff(times))>.009
    physical_gap = next(row["nearest_other_in_units_of_radius"] for row in indices
                        if row["j"]==8 and row["reference_spin"]==7)*min(abs(radius(t+.225)) for t in times)
    spread = .2*(np.hypot(np.hypot(.6,.45),np.sqrt(72)*(radius(1.95+.225)-radius(1.95-.225)))
                 +np.hypot(.6,.45))/18
    assert spread < physical_gap
    split_weight=sum(row["leading_received_weight"]/row["reference_copies"] for row in separated)
    unchanged=5*passage[1]["leading_received_weight"]/passage[1]["reference_copies"]
    return dict(crossings=materials, spatially_resolved=profiles,
                finite_passage=passage,relative_indices=indices,
                separated_reference=dict(j=8,copies=5,contacts=times,leading_received_weight=split_weight,
                                         coincident_five_copy_weight=unchanged,full_center_spread=spread,
                                         nearest_competing_level_lower_bound_at_own_contact=physical_gap),
                ordinary_matter=sea, material_spin=material_spin(), interior=phases_and_tags())


if __name__ == "__main__":
    result = main()
    path = ROOT / "verification" / "cat-contact-recoil-results.json"
    path.write_bytes((json.dumps(result, indent=2, allow_nan=False)+"\n").encode("utf-8"))
