"""Material writes with coherent recoil, in a finite gauge-singlet sector.

The output packet is retained by B. Each calculation uses the same energy
operator on spectator, receiver and recoil before and after a transition.
"""
import numpy as np


def bohr_components(before, after, source, tolerance=1e-11):
    ein, vin = np.linalg.eigh(before)
    eout, vout = np.linalg.eigh(after)
    components = {}
    for i, energy in enumerate(ein):
        for j, final in enumerate(eout):
            gap = energy - final
            amplitude = np.vdot(vout[:, j], source @ vin[:, i])
            if gap <= tolerance or abs(amplitude) <= tolerance:
                continue
            # The test Hamiltonians have exactly coincident gaps within tolerance.
            key = next((w for w in components if abs(w - gap) < tolerance), float(gap))
            term = amplitude * np.outer(vout[:, j], vin[:, i].conj())
            components[key] = components.get(key, 0) + term
    return components


def response(energy):
    return energy**3 * np.exp(-energy)


def packet_operator(parts):
    gaps = sorted(parts)
    recoil = np.diag([0.] + gaps)
    size = next(iter(parts.values())).shape[0]
    jump = np.zeros((size * len(recoil),) * 2, complex)
    for index, gap in enumerate(gaps, 1):
        shift = np.zeros_like(recoil)
        shift[index, 0] = 1
        jump += np.sqrt(response(gap)) * np.kron(parts[gap], shift)
    return jump, recoil


def norm(a):
    return float(np.linalg.norm(a, 2))


def check_energy():
    rng = np.random.default_rng(1839)
    v, _ = np.linalg.qr(rng.normal(size=(4, 4)) + 1j*rng.normal(size=(4, 4)))
    before = np.diag([0., 1., 3., 4.])
    after = (v * np.array([0., 1., 2., 4.])) @ v.conj().T
    source = rng.normal(size=(4, 4)) + 1j*rng.normal(size=(4, 4))
    source /= norm(source)
    parts = bohr_components(before, after, source)
    jump, recoil = packet_operator(parts)
    base = np.kron(before, np.eye(len(recoil))) + np.kron(np.eye(4), recoil)
    final = np.kron(after, np.eye(len(recoil))) + np.kron(np.eye(4), recoil)
    rate = jump.conj().T @ jump
    eig, vec = np.linalg.eigh(rate)
    step = .4/max(eig)
    quiet = (vec * np.sqrt(1-step*eig)) @ vec.conj().T
    # The extra unitary on the quiet branch is diagonal in the incoming energy.
    quiet = np.diag(np.exp(-1j*step*np.diag(base))) @ quiet
    write = np.sqrt(step)*jump
    identity = np.eye(len(rate))
    residuals = dict(intertwining=norm(final @ jump - jump @ base),
                     trace=norm(quiet.conj().T @ quiet + write.conj().T @ write - identity),
                     first_moment=norm(quiet.conj().T @ base @ quiet
                                       + write.conj().T @ final @ write - base),
                     second_moment=norm(quiet.conj().T @ base @ base @ quiet
                                        + write.conj().T @ final @ final @ write - base @ base))
    # Each distinct total-energy spectral projector is preserved as an observable.
    def projector(h, e):
        val, basis = np.linalg.eigh(h)
        sub = basis[:, abs(val-e) < 1e-9]
        return sub @ sub.conj().T
    residuals["spectral_measure"] = max(norm(quiet.conj().T @ projector(base,e) @ quiet
        + write.conj().T @ projector(final,e) @ write - projector(base,e))
        for e in np.unique(np.round(np.r_[np.linalg.eigvalsh(base),np.linalg.eigvalsh(final)],9)))
    assert max(residuals.values()) < 2e-12
    return dict(positive_gaps=sorted(parts),residuals=residuals)


def spectator():
    spectator_energy = np.diag([0., 3.])
    latch_energy = np.diag([0., 1.])
    before = np.kron(spectator_energy,np.eye(2)) + np.kron(np.eye(2),latch_energy)
    source = np.kron(np.eye(2), np.array([[0.,1.],[0.,0.]]))
    parts = bohr_components(before,before,source)
    assert len(parts) == 1
    component = parts[1.]
    np.testing.assert_allclose(component,source,atol=1e-15)
    # Entangle the spectator with a reference. Keep recoil and receiver at B.
    vector = np.zeros(8)
    vector[[1,7]] = 1/np.sqrt(2)
    target = np.zeros(8)
    target[[0,6]] = 1/np.sqrt(2)
    joint = np.kron(np.eye(2),component) @ vector
    good = float(abs(target @ joint)**2)
    incoming = [np.diag((np.diag(before)==e).astype(float)) for e in (1,4)]
    bad = float(sum(abs(target @ (np.kron(np.eye(2),component @ p) @ vector))**2
                    for p in incoming))
    assert abs(good-1)<1e-13 and abs(bad-.5)<1e-13
    return dict(coherent_gap_fidelity=good, archived_absolute_energy_fidelity=bad)


def framework_checks():
    j12 = np.diag([0.,2.])
    j23 = np.array([[1.5,np.sqrt(3)/2],[np.sqrt(3)/2,.5]])
    signed_volume = 1j*(j12 @ j23-j23 @ j12)
    signs = np.linalg.eigvalsh(signed_volume)
    np.testing.assert_allclose(signs,[-np.sqrt(3),np.sqrt(3)])
    a = np.array([[0.,1.],[0.,0.]])
    b = np.diag([1.,-1.])
    left,right = np.kron(a,np.eye(2)),np.kron(np.eye(2),b)
    assert np.array_equal(left @ right,right @ left)
    p = .2
    chain = np.array([[1-p,0.],[p,1.]])
    stationary = np.array([0.,1.])
    np.testing.assert_allclose(chain @ stationary,stationary)
    # Only a measure with zero support on the ready state can balance this chain.
    return dict(oriented_four_valent_flux=signs.tolist(),separate_receipts_commute=True,
                transfer_probability=p,reverse_probability=0.,stationary_ready_weight=0.)


def shared_interior():
    """The same amplitude must satisfy each populated material contact."""
    from scipy.linalg import expm
    mismatch = np.diag([0., 1.])
    identity = np.eye(2)
    h = np.array([[0., 1.], [1., 0.]])
    yes = np.zeros((2, 2))
    no = identity
    variants = {"near_common": ([yes, mismatch], [.5, .5]),
                "distant_closed": ([yes, mismatch, no], [.5, .25, .25]),
                "distant_refined": ([yes, mismatch, no, no], [.5, .25, .1, .15])}
    rows = {}
    for name,(arrows,weights) in variants.items():
        gram = sum(w * a.conj().T @ a for a,w in zip(arrows,weights))
        ev, basis = np.linalg.eigh(gram)
        keep = basis[:,ev < 1e-13]
        opened = keep @ keep.conj().T
        generator = np.pi/2 * np.kron(identity-opened,identity-h)
        routing = expm(-1j*generator)
        np.testing.assert_allclose(routing, np.kron(opened,identity)+np.kron(identity-opened,h),
                                   atol=3e-14)
        # One complete degenerate payload remains attached to either port.
        start = np.array([1.,0.,0.,0.])
        wave = (routing @ start).reshape(2,2)
        rows[name] = dict(gram=ev.tolist(),infall=float(np.linalg.norm(wave[:,0])**2),
                          surface=float(np.linalg.norm(wave[:,1])**2))
    assert rows["near_common"]["infall"] > 1-1e-12
    assert rows["distant_closed"]["infall"] < 1e-25
    np.testing.assert_allclose(rows["distant_closed"]["gram"],rows["distant_refined"]["gram"])
    return rows


def clifford_receipt():
    """Sixteen real supercharges on a positive-energy complex long multiplet."""
    basis = np.arange(256)
    conjugations = []
    for k in range(8):
        dest = basis ^ (1 << k)
        zstring = np.array([(-1)**(int(x) & ((1 << k)-1)).bit_count() for x in basis])
        zbit = 1-2*((basis >> k) & 1)
        for phase in (zstring,1j*zstring*zbit):
            conjugations.append((dest,phase))
    def conjugate(x, turn):
        dest, phase = turn
        result = np.zeros_like(x,dtype=complex)
        result[np.ix_(dest,dest)] = phase[:,None] * x * phase[None,:].conj()
        return result
    ident = np.eye(256)
    for i,(di,pi) in enumerate(conjugations):
        for j,(dj,pj) in enumerate(conjugations):
            assert np.array_equal(di[dj],dj[di])
            np.testing.assert_allclose(pj*pi[dj] + pi*pj[di], 2*float(i==j), atol=1e-14)
    seed = np.zeros((256,256),complex)
    seed[0,0] = 1.
    def average(x):
        for turn in conjugations:
            x = (x+conjugate(x,turn))/2
        return x
    completed = average(seed)
    np.testing.assert_allclose(completed,ident/256,atol=2e-15)
    assert all(np.array_equal(completed,conjugate(completed,t)) for t in conjugations)
    return dict(supercharges=len(conjugations),multiplet_dimension=len(basis),
                rate_per_component=float(abs(completed[0,0])**2),
                open_dimension_before_one_forbidden_polarization=255,
                invariant_open_dimension=int(np.count_nonzero(np.diag(completed)==0)))


def write_at_wall():
    # Two stored signs and two payload states. Orthogonal outgoing layer labels
    # consume the same blank precursor; the input may be entangled with a reference.
    sign_rotation = np.array([[1.,1.],[1.,-1.]])/np.sqrt(2)
    u = np.kron(sign_rotation,np.eye(2))
    code_energy = np.kron(np.eye(2),np.diag([0.,3.]))
    effects = []
    probabilities = []
    for i in range(2):
        proj = np.kron(np.diag([int(i==j) for j in range(2)]),np.eye(2))
        write = proj @ u
        np.testing.assert_allclose(code_energy @ write,write @ code_energy)
        effects.append(write.conj().T @ write)
        accepted = write[:,0:2]
        np.testing.assert_allclose(accepted.conj().T @ accepted,.5*np.eye(2))
        probabilities.append(float(np.vdot(accepted[:,0],accepted[:,0])))
    np.testing.assert_allclose(sum(effects),np.eye(4),atol=1e-14)
    return dict(two_signs=probabilities,unwritten_probability_given_incidence=0.,
                input_qubits=1,output_payload_qubits_per_selected_sign=1)


def calculate():
    return dict(conservation=check_energy(),retained_spectator=spectator(),
                alternative_discretizations=framework_checks(),common_interior=shared_interior(),supersymmetry=clifford_receipt(),surface_write=write_at_wall())
