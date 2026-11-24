"""Retarded layer response, a gauge-neutral receiver, and horizon tidal spectra."""

from math import factorial, pi
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.special import j0, jv, loggamma


def pulse_mode(k, signed_strength):
    """Positive-frequency in-mode -> alpha*out + beta*out-conjugate."""
    ell = (np.sqrt(1 + 4 * signed_strength + 0j) - 1) / 2
    ik = 1j * k
    alpha = np.exp(loggamma(1-ik) + loggamma(-ik)
                   - loggamma(1+ell-ik) - loggamma(-ell-ik))
    beta = 1j * np.sin(pi * ell) / np.sinh(pi * k)
    return alpha, beta


def integrate_mode(k, strength):
    cutoff = 19.
    start = np.exp(1j*k*cutoff)

    def wave(x, state):
        return state[1], -(k*k + strength/np.cosh(x)**2)*state[0]

    f, v = solve_ivp(wave, (-cutoff, cutoff), [start, -1j*k*start],
                     method="DOP853", rtol=4e-12, atol=2e-13).y[:, -1]
    phase = np.exp(1j*k*cutoff)
    return (f+1j*v/k)*phase/2, (f-1j*v/k)/phase/2


def retained_readout(kp, kq, strength):
    t = np.array([[1 / pulse_mode(k, s*strength)[0].conjugate()
                   for s in (1, -1)] for k in (kp, kq)])
    weight = abs(t.prod())**2
    probability = weight * abs(np.linalg.det(t))**2 / 8
    accepted = weight * np.prod(np.sum(abs(t)**2, axis=1)) / 4
    # Independent projection in the four-dimensional retained Fock space.
    state = np.kron(t[0], t[1]) * np.sqrt(weight)/2
    odd = np.array([0, 1, -1, 0])/np.sqrt(2)
    np.testing.assert_allclose([probability, accepted],
                               [abs(odd @ state)**2, np.vdot(state, state).real],
                               rtol=3e-11, atol=2e-25)
    return float(probability), float(accepted)


def layer_front(n, time, wave_number, radius=1.):
    """Response to unit integrated source on layer zero, at the antipode."""
    a = 2*pi*radius/n
    indices = np.arange(n)
    omega = np.hypot(wave_number, 2*np.sin(pi*indices/n)/a)
    return float(np.sum((-1.)**indices * time * np.sinc(omega*time/pi))/(n*a))


def image_front(time, wave_number, radius=1.):
    circumference = 2*pi*radius
    distances = np.arange(circumference/2, time, circumference)
    # Two images of each positive distance. Each image carries one half.
    return float(np.sum(j0(wave_number*np.sqrt(time*time-distances**2))))


def retarded_checks():
    rows = []
    for n in (4, 6, 10, 16):
        m, a = n//2, 2*pi/n
        adjacency = np.roll(np.eye(n, dtype=int), 1, axis=0)
        lap = 2*np.eye(n, dtype=int) - adjacency - adjacency.T
        for degree in range(m):
            assert np.linalg.matrix_power(lap, degree)[m, 0] == 0
        assert np.linalg.matrix_power(lap, m)[m, 0] == (-1)**m*2
        wave_number = .45
        op = lap/a**2 + wave_number**2*np.eye(n)
        gen = np.block([[np.zeros_like(op), np.eye(n)], [-op, np.zeros_like(op)]])
        for t in (.8, 2.2, 3.6, 5.):
            np.testing.assert_allclose(expm(t*gen)[m, n]/a,
                                       layer_front(n, t, wave_number), atol=2e-14)
            bessel = sum(quad(lambda x: jv(order, x), 0, 2*t/a, epsabs=1e-14)[0]
                         for order in range(n, 2*n+int(2*t/a)+30, 2*n))
            np.testing.assert_allclose(bessel, layer_front(n, t, 0.), atol=2e-14)
        # A local return lobe removes net charge without sourcing the receiver.
        neutral = np.eye(n, dtype=int)[:, 0] - np.eye(n, dtype=int)[:, 1]
        assert np.sum(neutral) == 0
        for degree in range(m-1):
            assert (np.linalg.matrix_power(lap, degree) @ neutral)[m] == 0
        assert (np.linalg.matrix_power(lap, m-1) @ neutral)[m] == -(-1)**(m-1)
        # The first point-impulse coefficient is 2/a^(2m+1)/(2m+1)!.
        rows.append(dict(layers=n, distance=m, impulsive_probability_power=4*m+4,
                         adjacent_neutral_probability_power=4*m,
                         impulse_coefficient=2/(a**(2*m+1)*factorial(2*m+1)),
                         prefront=layer_front(n, .75*pi, wave_number)))
    for time in (1., 2., .95*pi):
        assert image_front(time, .45) == 0.
    # The massive image solution also solves the time equation after Fourier
    # transformation. Compare spatially localized kernels in Laplace space.
    for laplace_frequency in (.55, 1.2):
        k = .45
        val = 0.
        for wrap in range(15):
            lo, hi = (2*wrap+1)*pi, (2*wrap+3)*pi
            val += quad(lambda t: np.exp(-laplace_frequency*t)*image_front(t, k),
                        lo, hi, epsabs=2e-13)[0]
        mass = np.hypot(laplace_frequency, k)
        np.testing.assert_allclose(val, 1/(2*mass*np.sinh(pi*mass)), rtol=2e-11)
    # Profiles are identical on the two discretizations, including zero mode.
    modes = np.arange(-4, 5)
    profile = np.exp(-.2*modes**2)*np.cos(.7*modes)
    for n in (12, 32, 64):
        a = 2*pi/n
        for t in (.1, 1., 3.2):
            continuum_w = np.hypot(.45, modes)
            direct_w = np.hypot(.45, 2*np.sin(a*modes/2)/a)
            kernel = t*(np.sinc(direct_w*t/pi)-np.sinc(continuum_w*t/pi))
            bound = a**2*t**2*np.sum(abs(profile)*abs(modes)**3)/48
            assert abs(profile @ kernel) <= bound
    return rows


def quadrupole_map(q):
    """Dimensionless r^5 d_i d_j d_k d_l (1/r) Q_kl, at n=z."""
    n = np.array([0., 0., 1.])
    qn, nn = q@n, np.outer(n, n)
    u = n@qn
    return 105*u*nn - 15*(np.eye(3)*u + 2*np.outer(qn, n) + 2*np.outer(n, qn)) + 6*q


def independent_hessian(q, step):
    point = np.array([0., 0., 1.])
    basis = np.eye(3)

    def quad_potential(x):
        return 3 * (x@q@x) / np.linalg.norm(x)**5

    result = np.empty((3, 3))
    for i in range(3):
        for j in range(3):
            result[i, j] = sum(s*t*quad_potential(point + step*(s*basis[i]+t*basis[j]))
                               for s in (-1, 1) for t in (-1, 1))/(4*step**2)
    return result


def stf_components():
    basis = [np.diag([-1., -1., 2.])/np.sqrt(6), np.diag([1., -1., 0.])/np.sqrt(2)]
    for i, j in ((0, 1), (0, 2), (1, 2)):
        shear = np.zeros((3, 3)); shear[i, j] = shear[j, i] = 1/np.sqrt(2)
        basis.append(shear)
    return basis


def spectrum_check():
    for q, eig in zip(stf_components(), [36, 6, 6, -24, -24]):
        h = .001
        fd = (4*independent_hessian(q, h/2)-independent_hessian(q, h))/3
        np.testing.assert_allclose(fd, eig*q, atol=2e-8)
        np.testing.assert_allclose(quadrupole_map(q), eig*q, atol=2e-14)
    def shifted_transform(u):
        return quad(lambda t: np.cos(u*t)/np.cosh(t/2)**6, -32., 32., epsabs=2e-13)[0]
    for u in (-1.1, -.1, .00001, .3, 1.3):
        spectrum = pi*u*(1+u*u)*(4+u*u)/(-2*np.expm1(-2*pi*u))
        np.testing.assert_allclose(spectrum, np.exp(pi*u)*shifted_transform(u)/shifted_transform(0.),
                                   rtol=2e-11)
    # Set G, r_s, and Delta to one only to test algebra at three radii.
    for r in (11., 19., 73.):
        hawking_temp = 1/(4*pi)
        stf_power = 8*(1/180)*hawking_temp
        horizon = (np.array([6., -24.])/(2*r**5))**2 * (stf_power/2) / 8
        rindler = (1/(2*r*r))**5/(5*pi)
        np.testing.assert_allclose(horizon/rindler, [1., 16.])
    return dict(tidal_eigenvalues=[36, -24, 6], horizon_radial_to_tangential=16,
                accelerated_radial_to_tangential=1,
                tangential_coefficient_in_units_G_rs5_delta2_over_r10=1/(160*pi))


def exchange_checks():
    rng = np.random.default_rng(1132)
    results = []
    for d in (2, 3, 5):
        unit = np.eye(d*d)
        swap = unit.reshape(d, d, d, d).swapaxes(0, 1).reshape(d*d, d*d)
        even, odd = (unit+swap)/2, (unit-swap)/2
        raw = rng.normal(size=(d, d))+1j*rng.normal(size=(d, d))
        a = (raw+raw.conj().T)/2
        cp, cq = .61, .38
        vertex = cp*np.kron(a, np.eye(d)) + cq*np.kron(np.eye(d), a)
        forward = np.linalg.norm(odd@vertex@even)**2
        backward = np.linalg.norm(even@vertex@odd)**2
        expect = (cp-cq)**2*(d*np.trace(a@a).real-np.trace(a).real**2)/4
        np.testing.assert_allclose([forward, backward], [expect, expect], rtol=3e-14)
        ratio = (forward/np.trace(even))/(backward/np.trace(odd))
        results.append([d, float(ratio)])
    return results


def isotropic_record_times():
    """First entry and return for the full spin-one polarization pair."""
    identity = np.eye(9)
    swap = identity.reshape(3, 3, 3, 3).swapaxes(0, 1).reshape(9, 9)
    scalar = np.eye(3).reshape(9)/np.sqrt(3)
    singlet = np.outer(scalar, scalar)
    odd = (identity-swap)/2
    spin_two = (identity+swap)/2-singlet
    sectors = [singlet, spin_two, odd]
    cp = .5
    cq = .5*np.sin(pi/11)/np.sin(2*pi/11)
    vertices = [cp*np.kron(a, np.eye(3))+cq*np.kron(np.eye(3), a) for a in stf_components()]
    u, v = 5*(cp+cq)**2/3, (cp+cq)**2/3
    w, z = 3*(cp-cq)**2/4, 5*(cp-cq)**2/4
    chain = np.array([[-u, u, 0.], [v, -v-w, w], [0., z, -z]])
    for i, observable in enumerate(sectors):
        evolved = sum(J@observable@J-(J@J@observable+observable@J@J)/2 for J in vertices)
        np.testing.assert_allclose(evolved, sum(chain[j, i]*p for j, p in enumerate(sectors)),
                                   atol=2e-15)
    np.testing.assert_allclose(np.array([1., 5., 3.])@chain, 0., atol=2e-15)
    means = []
    for fraction in (1., .5, .1):
        transient = chain.copy()
        transient[1, 2] *= 1-fraction
        sink = np.array([0., fraction*w, 0.])
        for s in (.03, .9):
            raw = np.linalg.solve(s*np.eye(3)-transient, sink)
            first_two = w*(s+u)/(s*s+(u+v+w)*s+u*w)
            marked = fraction*first_two/(1-(1-fraction)*first_two*z/(z+s))
            np.testing.assert_allclose(raw[:2], [u/(u+s)*marked, marked], rtol=2e-14)
        mean = np.linalg.solve(-transient, np.ones(3))
        np.testing.assert_allclose([mean[0]-mean[1], mean[1]*z], [1/u, 3/fraction-1], rtol=2e-13)
        means.append(dict(marked_fraction=fraction, spin_two_wait_over_odd_lifetime=float(mean[1]*z)))
    t = 1e-4
    np.testing.assert_allclose(expm(t*chain)[0, 2], u*w*t*t/2, rtol=7e-5)
    # In type IIA the D0 mass and the Newton constant depend on the same g_s.
    for coupling, x, y, volume in ((1e-10, .1, .1, 10.), (1e-8, .2, .15, 2.)):
        length = 1.7
        newton = 8*pi**6*coupling**2*length**8/((2*pi*length)**6*volume)
        gap = x/(2*pi*length)
        recoil_time = np.sqrt((1/(coupling*length))*(x*length)/(2/(2*pi*length**2)))
        upper = newton*(y*gap)**5/gap**2/pi*recoil_time
        np.testing.assert_allclose(upper, coupling**1.5*x**3.5*y**5/(64*pi**3.5*volume),
                                   atol=0., rtol=2e-15)
    return dict(rates_in_units_of_stf_power=[u, v, w, z], singlet_second_order=u*w/2,
                marked_waits=means)


def reference_checks():
    for k, g in ((.8, .15), (1.3, 1.1), (.65, .32), (2., .8), (1.8, 2.)):
        for sign in (-1, 1):
            solution = np.array(pulse_mode(k, sign*g))
            ode = np.array(integrate_mode(k, sign*g))
            np.testing.assert_allclose(solution, ode, atol=1e-9)
            np.testing.assert_allclose(abs(solution[0])**2-abs(solution[1])**2, 1., atol=2e-13)
    n = 11
    kq = np.sin(2*pi/n)/np.sin(pi/n)
    rows = []
    for g in (.0003, .04, .2, .55, .9):
        probability, accepted = retained_readout(1., kq, g)
        weak = g*g*(1-1/kq)**2/2
        rows.append(dict(g=g, probability=probability, accepted=accepted, weak_pulse=weak))
    np.testing.assert_allclose(rows[0]["probability"], rows[0]["weak_pulse"], rtol=4e-7)
    assert retained_readout(1., 1., .3)[0] < 1e-28
    return dict(front=retarded_checks(), third_arm_gap=np.sin(3*pi/n)/np.sin(pi/n),
                second_arm_gap=kq, pulses=rows, horizon=spectrum_check(), balance=exchange_checks(),
                waiting=isotropic_record_times())


def draw_reference(root):
    import matplotlib.pyplot as plt
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.55, 3.25), layout="constrained")
    times = np.linspace(.25*pi, 1.7*pi, 380)
    for n, color in ((6, "#a75a2a"), (24, "#376d89"), (96, "#46794e")):
        left.plot(times/pi, [layer_front(n, t, .45) for t in times], color=color, label=f"{n} layers")
    x1, x2 = times[times < pi], times[times > pi]
    for x in (x1, x2):
        left.plot(x/pi, [image_front(t, .45) for t in x], color="black", ls="--", lw=1.2,
                  label="continuous circle" if x is x1 else None)
    left.set(xlabel=r"Time / antipodal travel time", ylabel="Retarded scalar response",
             title="How a gravitational pulse arrives")
    kq = np.sin(2*pi/11)/np.sin(pi/11)
    strength = np.geomspace(.015, .95, 140)
    exact = [retained_readout(1., kq, g)[0] for g in strength]
    right.loglog(strength, exact, color="#376d89", label="exact pulse")
    right.loglog(strength, strength**2*(1-1/kq)**2/2, "--", color="#a75a2a", label="weak pulse")
    right.set(xlabel=r"Pulse strength $e_0\tau^2$", ylabel="Odd probability per preparation",
              title="What the matrix loop retains")
    for ax in (left, right):
        ax.legend(frameon=False, fontsize=8)
        ax.spines[["top", "right"]].set_visible(False)
    fig.savefig(Path(root)/"manuscripts/matrix_polarization_reference.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)
