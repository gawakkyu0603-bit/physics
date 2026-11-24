"""Oriented matter at a CAT volume bounce, in the clock and length units of T.11."""
import json
import argparse
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.interpolate import CubicHermiteSpline
from scipy.linalg import expm
from scipy.optimize import brentq
from scipy.special import jv, ndtr

ROOT = Path(__file__).resolve().parents[1]
START, END = -.5, .5
ODE = dict(method="DOP853", rtol=1.5e-12, atol=2e-14, max_step=.012, dense_output=True)


def clifford():
    one = np.eye(2)
    x = np.array([[0, 1], [1, 0]])
    y = np.array([[0, -1j], [1j, 0]])
    z = np.diag([1, -1])
    matrices = []
    for position in range(4):
        for middle in (x, y):
            row = np.array([[1.]])
            for factor in [z]*position + [middle] + [one]*(3-position):
                row = np.kron(row, factor)
            matrices.append(row)
    return matrices


def spin_matrices(j):
    magnetic = np.arange(-j, j+1)
    raising = np.diag(np.sqrt((j-magnetic[:-1])*(j+magnetic[:-1]+1)), -1)
    return [(raising+raising.T)/2, (raising-raising.T)/2.0j, np.diag(magnetic)]


def free_initial(at=START):
    def rhs(t, y):
        return np.r_[y[2:], -2*np.dot(y[:2], y[:2])*y[:2]]
    sol = solve_ivp(rhs, (0., at), [1., 0., 0., .5], **ODE)
    assert sol.success
    return sol.y[:, -1]


def incident_tide(t, wave, shape="sandwich"):
    phase = (t+.49)/.10
    if not 0 < phase < 1:
        return 0.
    sine = np.sin(np.pi*phase)
    if shape == "compact_strain":
        # Second derivative of sin^6(pi*phase), normalized by 6 pi^2.
        return wave*(5*sine**4-6*sine**6)
    return wave*sine**4


def geometry(j, offset, speed=0., wave=0., scale=1., shape="sandwich"):
    inertia = (2*j+1)*j*(j+1)
    reduced = (2*j+1)/(2*j+2)

    def rhs(t, y):
        u, velocity = y[:2], y[2:4]
        d, v = y[4:6]
        tide = incident_tide(t, wave, shape)
        force = -2*np.dot(u, u)*u-tide*np.array([u[0], -u[1]])
        qdot = inertia*(u[0]*velocity[0]-u[1]*velocity[1])+reduced*d*v
        return np.r_[velocity, force, v, -tide*d, -tide*qdot]

    initial = free_initial(scale*START)*np.array([scale, scale, scale**2, scale**2])
    sol = solve_ivp(rhs, (START, END), [*initial, offset+speed*START, speed, 0.], **ODE)
    assert sol.success

    def energy(y):
        return (inertia*(np.dot(y[2:4], y[2:4])+np.dot(y[:2], y[:2])**2)+reduced*y[5]**2)/2

    energy_change = energy(sol.y[:, -1])-energy(sol.y[:, 0])
    assert abs(energy_change-sol.y[-1, -1]) < 2e-10*max(1., inertia)
    return sol.sol, float(energy_change)


class ChargedProbe:
    def __init__(self, j):
        self.j = j
        self.colors = round(2*j+1)
        self.gamma = clifford()
        spin = spin_matrices(j)
        self.first, self.second = (sum(np.kron(self.gamma[k+i], spin[i]) for i in range(3))
                                   for k in (0, 3))
        self.offset = np.kron(self.gamma[2], np.eye(self.colors))
        self.size = self.first.shape[0]

    def hamiltonian(self, state):
        return state[0]*self.first+state[1]*self.second-state[4]*self.offset

    def edge(self, state):
        u = state[:2]
        unit = u/np.linalg.norm(u)
        parallel = [unit[0]*self.gamma[i]+unit[1]*self.gamma[i+3] for i in range(3)]
        chirality = -1j*parallel[0]@parallel[1]@parallel[2]
        north = (np.eye(16)+chirality)@(np.eye(16)+parallel[2])/4
        eig, basis = np.linalg.eigh(north)
        assert sum(eig > .5) == 4
        highest = np.eye(self.colors)[:, -1:]
        return np.kron(basis[:, eig > .5], highest)

    def eigenvalue(self, state):
        a = np.linalg.norm(state[:2])
        return self.j*a-state[4]*state[0]/a


def propagate(probe, orbit, start, stop, vectors):
    def rhs(t, y):
        return (-1j*probe.hamiltonian(orbit(t))@y.reshape(vectors.shape)).ravel()
    sol = solve_ivp(rhs, (start, stop), vectors.ravel(), **ODE)
    assert sol.success
    return sol.y[:, -1].reshape(vectors.shape)


def counts(occupied, first, second):
    """Joint law of two actual occupation readings, dephasing only the first total count."""
    span, singular, _ = np.linalg.svd(np.column_stack((first, second)), full_matrices=False)
    basis = span[:, singular > 1.e-11]
    identity = np.eye(basis.shape[1])
    projection = []
    for columns in (first, second):
        small = basis.conj().T @ columns
        projection.append(small@small.conj().T)
    p, q = projection
    restricted = basis.conj().T@occupied
    covariance = restricted@restricted.conj().T
    count_size = max(first.shape[1], second.shape[1])+1
    roots = np.exp(2j*np.pi*np.arange(count_size)/count_size)
    generating = np.zeros((count_size, count_size), dtype=complex)
    for i, s in enumerate(roots):
        for k, z in enumerate(roots):
            for phase in roots:
                matrix = ((identity+(s*phase-1)*p)@(identity+(z-1)*q)
                          @(identity+(phase.conjugate()-1)*p))
                generating[i, k] += np.linalg.det(identity+covariance@(matrix-identity))/count_size
    table = np.fft.fft2(generating)/count_size**2
    assert np.max(abs(table.imag)) < 1e-11 and table.real.min() > -1e-11
    table = table.real.clip(min=0)
    assert abs(table.sum()-1) < 2e-10
    eigenvalues = np.linalg.eigvalsh(first.conj().T@occupied@occupied.conj().T@first)
    independent = np.array([1.])
    for particle in eigenvalues:
        independent = np.convolve(independent, [1-particle, particle])
    np.testing.assert_allclose(independent, table.sum(axis=1)[:len(independent)], atol=1e-11)
    return table, eigenvalues


def fock_check():
    # Two overlapping rank-two observables, with coherence within total count one.
    from itertools import combinations
    orbitals = np.eye(3)
    first = orbitals[:, :2]
    second = np.column_stack(([1/np.sqrt(2), 0., 1/np.sqrt(2)], [0., 1., 0.]))
    filled, _ = np.linalg.qr(np.array([[1, 1j], [1j, .7], [.2, 1]], dtype=complex))
    table, _ = counts(filled, first, second)
    pairs = list(combinations(range(3), 2))
    vector = np.array([np.linalg.det(filled[list(pair), :]) for pair in pairs])
    def number(columns):
        proj = columns@columns.conj().T
        exterior = np.kron(proj, np.eye(3))+np.kron(np.eye(3), proj)
        anti = np.column_stack([(np.kron(orbitals[:, a], orbitals[:, b])-
                                 np.kron(orbitals[:, b], orbitals[:, a]))/np.sqrt(2)
                                for a, b in pairs])
        values, vectors = np.linalg.eigh(anti.conj().T@exterior@anti)
        return [vectors[:, abs(values-i)<1e-8] for i in range(3)]
    p, q = number(first), number(second)
    direct = np.array([[np.linalg.norm(b.conj().T@a@(a.conj().T@vector))**2 for b in q] for a in p])
    np.testing.assert_allclose(direct, table[:3, :3], atol=2e-13)
    return float(np.max(abs(direct-table[:3, :3])))


def matter(j, ratio, wave):
    orbit, work = geometry(j, j*ratio, wave=wave)
    probe = ChargedProbe(j)
    def endpoint(t):
        return probe.eigenvalue(orbit(t))
    times = [brentq(endpoint, *interval) for interval in ((START, 0.), (0., END))]
    h0 = probe.hamiltonian(orbit(START))
    values, basis = np.linalg.eigh(h0)
    assert np.min(abs(values)) > 1e-4
    occupied = propagate(probe, orbit, START, times[0], basis[:, values < 0])
    first, second = [probe.edge(orbit(t)) for t in times]
    second_at_first = propagate(probe, orbit, times[1], times[0], second)
    table, occupations = counts(occupied, first, second_at_first)
    slopes, gaps = [], []
    for t in times:
        state = orbit(t)
        transverse = abs(state[4]*state[1])/np.linalg.norm(state[:2])
        actual = min(abs(np.linalg.eigvalsh(probe.hamiltonian(state))))
        np.testing.assert_allclose(actual, transverse, atol=2e-11)
        gaps.append(float(actual))
        slopes.append(float((endpoint(t+1e-5)-endpoint(t-1e-5))/2e-5))
    reach = quad(lambda t: np.linalg.norm(orbit(t)[2:4]), *times, epsabs=2e-13)[0]
    first_counts, second_counts = table.sum(axis=1), table.sum(axis=0)
    active = table > 1.e-15
    shared = np.sum(table[active]*np.log2((table/np.outer(first_counts, second_counts))[active]))
    return dict(spin=j, offset_over_j=ratio, incoming_tide=wave,
                contact_times=times, oriented_slopes=slopes, physical_gaps=gaps,
                first_edge_filling=occupations.tolist(), joint_counts=table.tolist(),
                equal_counts=float(table.trace()), first_count_entropy_bits=float(-first_counts@np.log2(first_counts)),
                count_mutual_information_bits=float(shared), low_frequency_longitudinal_reach=reach,
                relative_mechanical_work=work)


def curvature_and_contacts():
    rows = []
    for h in (.25, .5, .9, 1.1):
        def rhs(t, y):
            return np.r_[y[2:], -2*np.dot(y[:2], y[:2])*y[:2]]
        sol = solve_ivp(rhs, (0., .003), [1., 0., 0., h], **ODE)
        def scales(t):
            y = sol.sol(t)
            radius = np.sqrt(np.linalg.norm(y[2:]))
            return np.array([np.linalg.norm(y[:2])/radius, radius])
        step = .0005
        base = scales(0.)
        accel = (-2*scales(2*step)+32*scales(step)-30*base)/(12*step**2*h*base)
        difference = -accel[0]+accel[1]-1/h
        expected = (4-h*h-h**4)/h**3
        np.testing.assert_allclose(difference, expected, rtol=1e-8)
        volume = (2-h*h)*(1-h*h)/h**3
        np.testing.assert_allclose(accel[0]+2*accel[1], volume, rtol=2.e-8)
        rows.append(dict(tangential_speed=h, proper_volume_acceleration=volume,
                         radial_electric_weyl=expected/3, weyl_squared=4*expected**2/3))
    orbit, _ = geometry(1., 1.)
    def threshold(t):
        state = orbit(t)
        return np.dot(state[:2], state[:2])/state[0]
    moving, _ = geometry(1., 1., speed=.25)
    probe = ChargedProbe(1.)
    delta = 1e-4
    static_jet = (probe.eigenvalue(orbit(delta))+probe.eigenvalue(orbit(-delta))
                  -2*probe.eigenvalue(orbit(0.)))/delta**2
    moving_jet = (probe.eigenvalue(moving(delta))-probe.eigenvalue(moving(-delta)))/(2*delta)
    np.testing.assert_allclose([static_jet, moving_jet], [-1.5, -.25], atol=1e-7)
    return dict(curvature=rows, threshold_at_half=threshold(.5), static_second_derivative=static_jet,
                moving_first_derivative=moving_jet)


def charge_bridge():
    """On-shell ordinary, charge-compensated Yukawa link on two bouncing membranes."""
    rows = []
    for j in (1., 8., 32., 128.):
        mass = .6
        width = .8/np.sqrt(j*(j+1))
        frequency = np.hypot(mass, np.sqrt(j*(j+1))*width)
        fraction = (frequency+mass)/(2*(j+1)*mass)
        e_left = fraction*mass
        e_right = np.hypot((1-fraction)*mass, j*width)
        s = (frequency-mass)/(2*(frequency-e_left))
        sx = np.array([[0., 1.], [1., 0.]])
        sy = np.array([[0., -1j], [1j, 0.]])
        sz = np.diag([1., -1.])
        _, left = np.linalg.eigh(e_left*sx)
        _, right = np.linalg.eigh(-(1-fraction)*mass*sx-j*width*sz)
        explicit = abs(left[:, 1].conj()@sy@right[:, 0])**2
        np.testing.assert_allclose([e_left+e_right, explicit], [frequency, s], atol=4e-15)
        rows.append(dict(spin=j, right_sphere_scale=1-width, frequency=frequency,
                         normal_fraction=fraction, spin_factor=float(s),
                         vertex_squared_per_g_squared=float(s/(2*(2*j+1)*frequency))))
    return rows


def populated_bridge(j, nodes, wave=0., fixed_clock=False, shape="sandwich"):
    """Leading vacuum-to-compensated-transfer weight up to the first oriented contact."""
    probe = ChargedProbe(j)
    mass = .6
    width = .8/np.sqrt(j*(j+1))
    scale = 1-width
    fraction = (1+mass)/(2*(j+1)*mass)
    color = np.eye(probe.colors)
    normal = np.kron(probe.gamma[6], color)
    vertex = np.kron(probe.gamma[7], color)
    velocity = -.25*j
    spheres = [geometry(j, j, velocity, wave, factor, shape)[0] for factor in (1., scale)]
    def oriented(t):
        return probe.eigenvalue(spheres[0](t))
    contact = brentq(oriented, -.15, .12)
    assert max(oriented(t) for t in np.linspace(START, -.15, 31)) < 0
    stop = 0. if fixed_clock else contact
    def hamiltonian(t, right):
        state = spheres[int(right)](t)
        displacement = (fraction-int(right))*mass
        return (state[0]*probe.first+state[1]*probe.second
                -state[4]*probe.offset+displacement*normal)
    def spinors(right):
        e, v = np.linalg.eigh(hamiltonian(START, right))
        assert min(abs(e)) > 1e-4 and sum(e<0)*2 == len(e)
        def rhs(t, y):
            return (-1j*hamiltonian(t, right)@y.reshape(v.shape)).ravel()
        sol = solve_ivp(rhs, (START, stop), v.ravel(), **ODE)
        assert sol.success
        return lambda t: np.split(sol.sol(t).reshape(v.shape), 2, axis=1)
    def frequency(t):
        delta = spheres[0](t)[:2]-spheres[1](t)[:2]
        return np.sqrt(mass**2+j*(j+1)*np.dot(delta, delta))
    omega0 = frequency(START)
    initial = [1/np.sqrt(2*omega0), -1j*np.sqrt(omega0/2)]
    mode = solve_ivp(lambda t, y: [y[1], -frequency(t)**2*y[0]], (START, stop), initial, **ODE)
    assert mode.success
    left, right = spinors(False), spinors(True)
    half = probe.size//2
    amplitude = np.zeros((2, half, half), dtype=complex)
    times, weights = np.polynomial.legendre.leggauss(nodes)
    for node, weight in zip(times, weights):
        t = (START+stop+(stop-START)*node)/2
        lf, le = left(t)
        rf, re = right(t)
        coefficient = weight*(stop-START)/2*mode.sol(t)[0].conjugate()/np.sqrt(probe.colors)
        amplitude[0] += coefficient*le.conj().T@vertex@rf
        amplitude[1] += coefficient*re.conj().T@vertex@lf
    outward = float(np.linalg.norm(amplitude[0])**2)
    inward = float(np.linalg.norm(amplitude[1])**2)
    overlap = probe.edge(spheres[0](stop)).conj().T@left(stop)[1]@amplitude[0]
    v, dv = mode.sol(stop)
    assert abs(-2*(v.conjugate()*dv).imag-1) < 1e-10
    number = (abs(dv)**2+frequency(stop)**2*abs(v)**2)/(2*frequency(stop))-.5
    assert number > 0 and 0 < np.linalg.norm(overlap)**2 < outward
    inertia = probe.colors*j*(j+1)
    reduced = 2*probe.colors/(2*probe.colors+1)
    def mechanical_energy(t):
        states = [orb(t) for orb in spheres]
        internal = sum(y[2:4]@y[2:4]+(y[:2]@y[:2])**2 for y in states)
        return (inertia*internal+reduced*states[0][5]**2)/2
    def power(t):
        states = [orb(t) for orb in spheres]
        qdot = sum(y[0]*y[2]-y[1]*y[3] for y in states)
        return -incident_tide(t, wave, shape)*(inertia*qdot+reduced*states[0][4]*states[0][5])
    work = quad(power, -.49, -.39, epsabs=3e-13)[0]
    np.testing.assert_allclose(work, mechanical_energy(stop)-mechanical_energy(START), atol=5e-10)
    return dict(spin=j, incident_tide=wave, read_clock=stop, contact_clock=contact,
                relative_collective_work=work, outgoing_oscillator_number=float(number),
                plus_weight_per_g_squared=outward, minus_weight_per_g_squared=inward,
                extra_left_particle_edge_weight_per_g_squared=float(np.linalg.norm(overlap)**2))


def momentum_paths():
    rows = []
    angle = np.pi/4
    sx = np.array([[0., 1.], [1., 0.]])
    for k in (1, 2, 4, 10, 50):
        unitary = expm(-1j*angle*sx/k)
        state = np.diag([1., 0.])
        for _ in range(k):
            evolved = unitary@state@unitary.conj().T
            state = np.diag(np.diag(evolved))
        expected = (1-np.cos(2*angle/k)**k)/2
        np.testing.assert_allclose(state[1, 1].real, expected, atol=3e-14)
        rows.append(dict(resolved_intervals=k, final_transfer=float(expected)))
    # One identifiable unit of rank can migrate coherently between two locations.
    # A single final marking preserves all inclusive probabilities, also with
    # noncommuting propagation and finite-rank boundaries.
    bare = np.diag([-.4, .2, -.1])+np.diag([.7, .3], 1)+np.diag([.7, .3], -1)
    rotation = expm(-.7j*sx)
    w = np.zeros((6, 6), dtype=complex)
    for n in range(3):
        w[2*n:2*n+2, 2*n:2*n+2] = np.linalg.matrix_power(rotation, n)
    dressed = w@np.kron(bare, np.eye(2))@w.conj().T
    prob = abs(expm(-1.3j*bare)[:, 1])**2
    marked = (expm(-1.3j*dressed)@np.kron([0., 1., 0.], [1., 0.])).reshape(3, 2)
    np.testing.assert_allclose(np.sum(abs(marked)**2, axis=1), prob, atol=4e-14)
    return dict(fixed_total_rank_interferometer=rows, inclusive_final_rank=prob.tolist())


def received_fields():
    """A pure source-flag preparation and a local, finite-noise quadrature on a circular orbit."""
    rows = []
    for j in (4., 8., 16., 32.):
        casimir = np.sqrt(j*(j+1))
        time = .25
        x = casimir*time
        lattice_step = np.sqrt(2)/casimir
        def frequency(k):
            return 2*casimir*abs(np.sin(k/2))
        def variance(k):
            f = frequency(k)
            return (np.cos(f*time)**2+(time*np.sinc(f*time/np.pi))**2)/2
        noise = np.sqrt(quad(variance, 0, np.pi, epsabs=2e-13)[0]/np.pi)
        for n in (0, int(np.ceil(casimir/2))):
            coefficient = jv(2*n, 2*x)
            integral = quad(lambda k: np.cos(n*k)*np.cos(frequency(k)*time), 0, np.pi,
                            epsabs=3e-14)[0]/np.pi
            np.testing.assert_allclose(integral, coefficient, atol=3e-14)
            bound = 1. if n<=x else np.exp(-2*n*np.arccosh(n/x)+2*np.sqrt(n*n-x*x))
            assert abs(coefficient) <= bound
            rows.append(dict(spin=j, clock_time=time, step=n, distance=n*lattice_step,
                             low_frequency_reach=np.sqrt(2)*time, retarded_displacement=float(coefficient),
                             mean_response_bound=float(bound), noise=float(noise),
                             sign_reading_advantage=float(ndtr(abs(coefficient)/noise)-.5)))
    return rows


def pulse_at_bounce(grid, j, length):
    """Propagate a compact scalar packet through the two actual north contacts in a periodic box."""
    casimir = np.sqrt(j*(j+1))
    w = .10
    zeta = np.arange(grid)*length/grid
    zeta = np.where(zeta<length/2, zeta, zeta-length)
    packet = np.where(abs(zeta)<w, np.cos(.5*np.pi*zeta/w)**8, 0.)
    fourier = np.fft.rfft(packet)
    momenta = 2*np.pi*np.fft.rfftfreq(grid, d=length/grid)
    shift = momenta/(2*casimir)
    def orbital_rhs(t, y):
        return np.r_[y[2:], -2*np.dot(y[:2], y[:2])*y[:2]]
    duration = .51+max(shift)
    knots = np.linspace(0., duration, int(np.ceil(duration/.008))+1)
    future = solve_ivp(orbital_rhs, (0., duration), [1., 0., 0., .5], method="DOP853",
                       rtol=1.5e-12, atol=2e-14, max_step=.07, t_eval=knots)
    assert future.success
    orbit = CubicHermiteSpline(knots, future.y[:2].T, future.y[2:].T)
    def u(t):
        values = orbit(abs(t)).T
        return values*np.array([np.ones_like(t), np.sign(t)])
    def endpoint(t):
        a1, a2 = u(np.array([t]))[:, 0]
        return a1*a1+a2*a2-.93*a1
    stop = brentq(endpoint, 0., END)
    def dynamics(t, y):
        displacement = u(t+shift)-u(t-shift)
        omega2 = casimir**2*np.sum(displacement**2, axis=0)
        position, velocity = np.split(y, 2)
        return np.r_[velocity, -omega2*position]
    count = len(fourier)
    solution = solve_ivp(dynamics, (-stop, stop), np.r_[np.ones(count), np.zeros(count)],
                         method="DOP853", rtol=5e-11, atol=3e-13, max_step=.024)
    assert solution.success
    auto = np.fft.irfft(abs(fourier)**2*solution.y[:count, -1], n=grid)
    auto /= np.dot(packet, packet)
    return [float(auto[round(distance*grid/length)]) for distance in (0., .75, 1.5)]


def main():
    samples = [matter(j, .93, wave) for j, wave in ((.5, 0.), (1., 0.), (2., 0.), (1., -.8))]
    quiet = np.array(samples[1]["joint_counts"])
    signal = np.array(samples[-1]["joint_counts"])
    total_variation = abs(quiet-signal).sum()/2
    assert total_variation > 1e-6
    assert samples[-1]["relative_mechanical_work"] > 0
    boxes = []
    for j in (2., 8.):
        coarse = pulse_at_bounce(1024, j, 12.)
        fine = pulse_at_bounce(2048, j, 12.)
        extended = pulse_at_bounce(4096, j, 24.)
        np.testing.assert_allclose(coarse, fine, atol=3e-6)
        np.testing.assert_allclose(extended, fine, atol=2e-7)
        boxes.append(dict(spin=j, separation=[0., .75, 1.5], grid1024=coarse,
                          grid2048=fine, extended_box=extended))
    pairs = []
    for j, wave, fixed in ((1., 0., False), (2., 0., False), (1., -.08, False),
                           (1., -.8, False), (1., -.8, True)):
        row = populated_bridge(j, 32, wave, fixed)
        refined = populated_bridge(j, 64, wave, fixed)
        np.testing.assert_allclose(list(row.values()), list(refined.values()), atol=2e-12)
        pairs.append(refined)
    linear = []
    for step in (.004, .002):
        plus = populated_bridge(1., 32, step)
        minus = populated_bridge(1., 32, -step)
        linear.append({key: (plus[key]-minus[key])/(2*step)
                       for key in ("contact_clock", "relative_collective_work", "plus_weight_per_g_squared")})
    np.testing.assert_allclose(list(linear[0].values()), list(linear[1].values()), rtol=5e-5)
    compact = []
    for moment in (0, 1):
        value = quad(lambda t: t**moment*incident_tide(t, 1., "compact_strain"), -.49, -.39)[0]
        assert abs(value) < 3e-15
    for step in (.016, .008):
        plus = populated_bridge(1., 48, step, True, "compact_strain")
        minus = populated_bridge(1., 48, -step, True, "compact_strain")
        compact.append((plus["plus_weight_per_g_squared"]-minus["plus_weight_per_g_squared"])/(2*step))
    assert abs(compact[1]) > 1e-8 and abs(compact[1]-compact[0]) < .002*abs(compact[1])
    result = dict(geometry=curvature_and_contacts(), preparations=samples,
                  explicit_fock_residual=fock_check(), two_pulse_decision=dict(
                      total_variation=float(total_variation),
                      optimal_equal_prior_success=float((1+total_variation)/2)),
                  compensated_contact=charge_bridge(), early_charge_transfer=pairs,
                  tidal_response_derivatives=linear, compact_strain_fixed_clock_response=compact,
                  longitudinal=momentum_paths(),
                  circular_receivers=received_fields(), compact_packet=boxes)
    out = ROOT/"verification"/"cat-oriented-bounce-results.json"
    out.write_text(json.dumps(result, indent=2, allow_nan=False)+"\n", encoding="utf8")
    print(f"Checked {len(samples)} preparations; written {out.name}")


def figure(destination):
    import matplotlib.pyplot as plt
    orbit, _ = geometry(1., 1.)
    times = np.linspace(START, END, 351)
    state = orbit(times)
    a = np.linalg.norm(state[:2], axis=0)
    radius = np.sqrt(np.linalg.norm(state[2:4], axis=0))
    fig, axes = plt.subplots(1, 2, figsize=(8.0, 3.05), layout="constrained")
    axes[0].plot(times, radius/radius[len(times)//2], color="#265c86", label="Sphere radius")
    axes[0].plot(times, a*radius/radius[len(times)//2], "--", color="#8d3d31", label="Cell volume")
    axes[0].set(xlabel="Matrix clock", ylabel="Relative to the turn", title="Geometry read by matter")
    for d, style, color, label in [(np.ones_like(times), "--", "#265c86", "Point at the pole"),
                                   (.93*np.ones_like(times), "-", "#8d3d31", "Point just inside"),
                                   (1-.25*times, ":", "#274f38", "Moving point")]:
        axes[1].plot(times, a-d*state[0]/a, style, color=color, label=label)
    axes[1].axhline(0., color=".45", linewidth=.7)
    axes[1].set(xlabel="Matrix clock", ylabel="Oriented level / spin", title="Charge-sensitive matter level")
    for ax in axes:
        ax.legend(frameon=False, fontsize=8)
        ax.spines[["right", "top"]].set_visible(False)
    fig.savefig(destination, metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path, help="Recreate the publication figure at this PDF path")
    args = parser.parse_args()
    if args.figure:
        figure(args.figure)
    else:
        main()
