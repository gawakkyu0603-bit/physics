"""Two-graviton curvature contact and a supported plane-wave matrix receiver."""
import itertools
from math import pi, sqrt
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigvalsh
from numpy.polynomial import Polynomial
import matplotlib.pyplot as plt


def curvature_vertex():
    """Contract linearized Riemann tensors with the Minkowski metric, without helicity formulas."""
    metric = np.array([-1., 1., 1., 1.])
    raising = np.einsum("a,b,c,d->abcd", metric, metric, metric, metric)
    pol = np.zeros((2, 4, 4))
    pol[0, 1, 1], pol[0, 2, 2] = 1/sqrt(2), -1/sqrt(2)
    pol[1, 1, 2] = pol[1, 2, 1] = 1/sqrt(2)

    def wave(direction, polarization):
        k = np.array([-1., 0., 0., direction])
        elem = np.einsum("a,c,bd->abcd", k, k, polarization)
        return (elem + elem.transpose(1, 0, 3, 2)
                - elem.swapaxes(0, 1) - elem.swapaxes(2, 3))/2

    waves = [[wave(sign, e) for e in pol] for sign in [1, -1]]
    opposite = np.array([[2*np.sum(left*right*raising) for right in waves[1]]
                         for left in waves[0]])
    parallel = np.array([[2*np.sum(left*right*raising) for right in waves[0]]
                         for left in waves[0]])
    s = 4.
    assert np.max(abs(opposite-np.eye(2)*s**2/2)) < 2e-14
    assert np.max(abs(parallel)) < 2e-14
    cross_section = np.sum(opposite**2)**2/4/(32*pi*s)
    spectral = np.sum(opposite**2)/(16*pi)
    assert abs(cross_section/(s**7/(512*pi))-1) < 2e-14
    assert abs(spectral/(s**4/(32*pi))-1) < 2e-14
    bright = np.eye(2)/sqrt(2)
    dark = np.diag([1., -1.])/sqrt(2)
    ratios = [(np.sum(opposite*state)**2)/(np.sum(opposite**2)/4) for state in [bright, dark]]
    assert np.allclose(ratios, [4., 0.]) and np.allclose(bright@bright.T, dark@dark.T)
    # Per invariant mass ds, impose a three-momentum cutoff L only to exhibit the divergence.
    boosts = []
    for cutoff in [4., 16., 64., 256.]:
        vol = quad(lambda k: 2*pi*k*k/sqrt(1+k*k), 0, cutoff)[0]
        exact = pi*(cutoff*sqrt(1+cutoff**2)-np.arcsinh(cutoff))
        assert abs(vol/exact-1) < 2e-12
        boosts.append([cutoff, float(vol/(pi*cutoff**2))])
    return dict(opposed_vertex=opposite.tolist(), parallel_vertex=parallel.tolist(),
                bright_dark_relative=ratios, normalized_boost_volume=boosts)


def chiral_matching():
    """Compare the quartic Weyl invariant using four actual on-shell tensor waves."""
    sign = np.array([-1., 1., 1., 1.])
    raising = np.einsum("a,b,c,d->abcd", sign, sign, sign, sign)
    dual = np.zeros((4, 4, 4, 4))
    for perm in itertools.permutations(range(4)):
        inversions = sum(a>b for i, a in enumerate(perm) for b in perm[i+1:])
        dual[perm] = (-1)**inversions*sign[perm[2]]*sign[perm[3]]/2
    def wave(angle, handedness, energy):
        n = np.array([np.sin(angle), 0., np.cos(angle)])
        tangent = np.array([np.cos(angle), 0., -np.sin(angle)])
        vector = np.r_[0., (tangent+1j*handedness*np.array([0., 1., 0.]))/sqrt(2)]
        p = energy*np.r_[-1., n]
        term = np.einsum("a,c,b,d->abcd", p, p, vector, vector)
        curv = (term+term.transpose(1, 0, 3, 2)-term.swapaxes(0, 1)-term.swapaxes(2, 3))/2
        star = np.einsum("ijab,abkl->ijkl", dual, curv)
        assert min(np.linalg.norm(star-1j*curv),np.linalg.norm(star+1j*curv)) < 5e-14
        return (curv-1j*star)/2, (curv+1j*star)/2
    def dot(a,b):
        return np.sum(a*b*raising)
    angles = []
    for theta in [pi/2, pi/3, .43, 1.27]:
        summed, factorized, nonzero = 0., 0., 0
        for hands in itertools.product([-1, 1], repeat=4):
            cs = [wave(z,h,e) for z,h,e in zip([0,pi,theta,theta+pi],hands,[-1,-1,1,1])]
            total, in_pairs = 0j, 0j
            for i,j in itertools.combinations(range(4),2):
                k,l = [idx for idx in range(4) if idx not in (i,j)]
                term = 4*dot(cs[i][0],cs[j][0])*dot(cs[k][1],cs[l][1])
                total += term
                if (i,j) in [(0,1),(2,3)]:
                    in_pairs += term
            if hands[0] == hands[1]:
                assert abs(total-in_pairs) < 1e-12
            else:
                assert abs(in_pairs) < 1e-12
            summed += abs(total)**2
            factorized += abs(in_pairs)**2
            nonzero += int(abs(total)>1e-10)
        assert nonzero == 6
        angle_weight = 1+((1-np.cos(theta))/2)**8+((1+np.cos(theta))/2)**8
        assert abs(summed/factorized-angle_weight)<5e-13
        angles.append(dict(angle=float(theta), weight=float(summed/factorized),
                           factorized=float(factorized), nonzero=nonzero))
    ratio = angles[0]["weight"]/angles[1]["weight"]
    assert abs(ratio-33024/36049)<3e-14
    return dict(angles=angles, right_angle_to_sixty=float(ratio))


def rotational_readout():
    """Two rotors in the total spin-zero sector. Basis L is the angular momentum of either rotor."""
    from scipy.special import roots_legendre, eval_legendre
    from scipy.linalg import eigh

    x, weights = roots_legendre(96)
    lvals = np.arange(72)
    jacobi = (lvals[:-1]+1)/np.sqrt((2*lvals[:-1]+1)*(2*lvals[:-1]+3))
    cos_matrix = np.diag(jacobi,1)+np.diag(jacobi,-1)
    p2_matrix = (3*cos_matrix@cos_matrix-np.eye(len(lvals)))/2
    p2 = (3*x*x-1)/2
    table = np.array([np.sqrt(2*l+1)*eval_legendre(l, x) for l in lvals])
    rows = []
    for shift, ratio0, energy0 in [(0., 9/5, 24/35), (-2., 1/20, 144/35)]:
        field = p2**2+shift*p2
        mat = p2_matrix@p2_matrix+shift*p2_matrix
        weak_ratio = (mat[4,0]/mat[2,0])**2
        assert abs(weak_ratio-ratio0)<2e-14
        energy_integral = np.dot(weights*(1-x*x),(3*x*(2*p2+shift))**2)/2
        assert abs(energy_integral-energy0)<2e-13
        eig, vec = eigh(mat)
        impulses = []
        for area in [.15,1.2,3.7]:
            amplitudes = table@(weights*np.exp(-1j*area*field))/2
            by_matrix = vec@(np.exp(-1j*area*eig)*vec[0])
            assert np.max(abs(amplitudes-by_matrix)) < 9e-13
            probabilities = abs(amplitudes)**2
            energy = np.dot(probabilities,lvals*(lvals+1))
            assert abs(np.sum(probabilities)-1)<3e-13
            assert sum(probabilities[1::2])<1e-25
            assert abs(energy/area**2-energy0)<3e-12
            impulses.append(dict(area=area, marginals=probabilities[:13:2].tolist(),
                                 energy=float(energy)))
        rows.append(dict(shift=shift, weak_ratio=float(weak_ratio), energy_coefficient=float(energy_integral),
                         impulses=impulses))
    return rows


def spacelike_insertions():
    """Two source insertions contracted with a full symmetric-tensor propagator."""
    sign = np.array([-1., 1., 1., 1.])
    raising = np.einsum("a,b,c,d->abcd", sign, sign, sign, sign)
    e = np.diag([0., 1., -1., 0.])/sqrt(2)

    def curvature(k, h):
        term = np.einsum("a,c,bd->abcd", k, k, h)
        return (term+term.transpose(1, 0, 3, 2)-term.swapaxes(0, 1)-term.swapaxes(2, 3))/2

    def vertex(k, ell):
        external = curvature(k, e)*raising
        result = np.zeros((4, 4))
        for i, j in itertools.product(range(4), repeat=2):
            unit = np.zeros_like(e)
            unit[i, j] = 1.
            result[i, j] = 2*np.sum(external*curvature(ell, (unit+unit.T)/2))
        return result

    rows = []
    for w, q in [(.3, .8), (1., 1.7), (2., 2.6)]:
        amp = 0.
        for ell_z in [q-w, q+w]:
            ell = np.array([0., 0., 0., ell_z])
            left = vertex(np.array([-w, 0, 0, w]), ell)
            right = vertex(np.array([-w, 0, 0, -w]), -ell)
            assert max(np.linalg.norm(ell@left), np.linalg.norm(ell@right)) < 1e-12
            tensor_part = np.sum(left*right*sign[:, None]*sign[None, :])
            traces = np.dot(sign,left.diagonal())*np.dot(sign,right.diagonal())
            amp += (tensor_part-traces/2)/ell_z**2
        value = 8*w**4*(q*q+w*w)
        assert abs(amp/value-1) < 3e-14
        rows.append(dict(w=w, q=q, amplitude=float(amp)))
    window = quad(lambda x: x*x*(1-x*x)**4, 0., 1.)[0]
    gaussian = quad(lambda x: x**11*np.exp(-x*x), 0., np.inf)[0]
    assert abs(window-128/3465)<1e-14 and abs(gaussian-60)<1e-10
    # The retarded wave equation integrates once in each null coordinate.
    def second(x):
        return (x*x-1)*np.exp(-x*x/2)
    def fourth(x):
        return (x**4-6*x*x+3)*np.exp(-x*x/2)
    pump = quad(lambda v: second(v)*second(v-.7), -12, 12, epsabs=1e-13)[0]
    for u in [-1.8,-.4,1.]:
        retarded = 2*pump*quad(fourth, -12., u, epsabs=1e-13)[0]
        analytic = 2*pump*u*(3-u*u)*np.exp(-u*u/2)
        assert abs(retarded-analytic) < 2e-13
    return dict(two_insertions=rows, worldline_phase_space=window, gaussian_zero_gap=gaussian,
                opposite_pump_overlap=float(pump))


def spherical_generators(rank):
    m = np.arange(rank)-(rank-1)/2
    up = np.diag(np.sqrt((rank-1)/2*((rank-1)/2+1)-m[:-1]*(m[:-1]+1)), -1)
    return [(up+up.T)/2, (up-up.T)/(2j), np.diag(m)]


def matrix_hessian(rank, fraction):
    """Differentiate the full vector force in the original matrices by real finite differences."""
    gen = spherical_generators(rank)
    herm = [np.diag(np.eye(rank)[i]).astype(complex) for i in range(rank)]
    for i in range(rank):
        for k in range(i):
            elem = np.zeros((rank, rank), complex)
            elem[i, k] = 1/sqrt(2)
            herm.extend([elem+elem.T, 1j*(elem-elem.T)])
    basis = np.array(herm)
    radius = fraction
    tide = -(radius-1)*(2*radius-1)
    center = radius*np.array(gen)

    def force(x):
        curl = np.array([x[i]+1j*(x[(i+1)%3]@x[(i+2)%3]-x[(i+2)%3]@x[(i+1)%3])
                         for i in range(3)])
        out = curl+tide*x
        for i in range(3):
            j, k = (i+1)%3, (i+2)%3
            out[i] += 1j*(x[j]@curl[k]-curl[k]@x[j]-x[k]@curl[j]+curl[j]@x[k])
        return out

    size = 3*rank**2
    hessian = np.empty((size, size))
    step = 2e-5
    for n in range(size):
        variation = np.zeros_like(center)
        variation[n//rank**2] = step*basis[n % rank**2]
        column = (force(center+variation)-force(center-variation))/(2*step)
        hessian[:, n] = np.einsum("kij,aji->ak", basis, column).real.ravel()
    expected = []
    for j in range(rank):
        for t, multiplicity in [(j, 2*j+3), (-1, 2*j+1 if j else 0), (-j-1, max(2*j-1, 0))]:
            expected += [radius*(t+1)*(radius*t+3-2*radius)]*multiplicity
    assert len(expected) == size
    error = float(np.max(abs(eigvalsh(hessian)-sorted(expected))))
    assert error < 5e-9
    # The six SO(6) polarizations have the same adjoint Hessian.
    def transverse(b):
        result = (.25-tide/2)*b
        for x in center:
            comm = x@b-b@x
            result += x@comm-comm@x
        return result
    transverse_hessian = np.array([np.einsum("kij,ji->k", basis, transverse(b)).real for b in basis])
    yspec = sorted([radius**2*j*(j+1)+.25-tide/2 for j in range(rank) for _ in range(2*j+1)])
    assert np.max(abs(eigvalsh(transverse_hessian)-yspec)) < 3e-12
    return dict(rank=rank, radius=radius, tide=tide, vector_error=error,
                minimum_transverse=float(min(yspec)))


def barrier_data(epsilon):
    """Stable integral and independent factored/closed expressions in units M=a=1."""
    f = (3+epsilon)/4
    d = 1-f
    beta = sqrt(d)
    upper = 2*f-1
    # Rationalize the width to retain relative precision close to the fold.
    width = epsilon*(3+epsilon)/(4*(upper+beta))
    action = 2*width**2.5*quad(lambda t: (1-t)*sqrt(t*(2*beta+width*t)),
                              0., 1., epsabs=1e-13, epsrel=1e-13)[0]
    if .005 < epsilon < .9999:
        root = sqrt(upper**2-d)
        closed = upper*(upper*root-d*np.arccosh(upper/beta))-2*root**3/3
        assert abs(closed/action-1) < 6e-10
    h = (1-epsilon**2)/8
    saddle = (3-epsilon)/4
    pot = lambda r: .5*r*r*((1-r)**2+h)
    if epsilon > .001:
        assert abs((pot(saddle)-pot(f))/(epsilon**3/32)-1) < 5e-7
    return dict(epsilon=epsilon, tide=h, action=float(action),
                scaled=float(action/epsilon**2.5), omega2=f*epsilon)


def smooth_tide(target, duration):
    # Quintic Hermite polynomial in elapsed fraction. Match the final free acceleration
    # as well as the two velocities and the initial acceleration. The tide is continuous.
    endpoint_accel = -target*(target-1)*(2*target-1)
    step = Polynomial([0, 0, 0, 10, -15, 6])
    endpoint = Polynomial([0, 0, 0, .5, -1, .5])
    path = Polynomial([1.])+(target-1)*step+duration**2*endpoint_accel*endpoint
    vel, acc, jerk = [path.deriv(k)/duration**k for k in (1, 2, 3)]

    def field(t):
        u = t/duration
        r = path(u)
        return -acc(u)/r-(r-1)*(2*r-1)

    def derivative(t):
        u = t/duration
        r = path(u)
        return -jerk(u)/r+acc(u)*vel(u)/r**2-(4*r-3)*vel(u)
    return field, derivative, path


def memory_paths():
    duration = 3.
    sol = []
    read = []
    for target in [.25, .75]:
        tide, tide_slope, path = smooth_tide(target, duration)
        assert min(path(np.linspace(0, 1, 201))) > 0
        assert abs(tide(0))+abs(tide(duration)) < 2e-13

        def forced(t, state):
            r, v, _ = state
            return v, -r*((r-1)*(2*r-1)+tide(t)), .5*r*r*tide_slope(t)

        pre = solve_ivp(forced, [0, duration], [1., 0., 0.], method="DOP853",
                        dense_output=True, rtol=3e-12, atol=3e-14)
        assert pre.success
        r, v, work = pre.y[:, -1]
        assert max(abs(r-target), abs(v), abs(work-9/512)) < 1e-10
        free = solve_ivp(lambda t, y: [y[1], -y[0]*(y[0]-1)*(2*y[0]-1)],
                         [0, 36], [r, v], method="DOP853", dense_output=True,
                         rtol=3e-12, atol=3e-14)
        assert free.success
        sol.append(free)
        read.append(dict(target=target, final_radius=float(r), final_velocity=float(v),
                         supplied_work=float(work), max_control=float(max(abs(tide(np.linspace(0, duration, 501)))))))
    times = np.linspace(0., 36., 721)
    lo, hi = [s.sol(times)[0] for s in sol]
    assert np.max(abs(lo+hi-1)) < 2e-10
    gap = hi**2-lo**2
    assert min(gap) >= .5-3e-10
    # A later identical small tide f^{(5)} of compact support reads the memory.
    # f=(1-z²)^7 on |z|<=1 has six continuous derivatives across its endpoints.
    f = Polynomial([1., 0., -1.])**7
    width, middle = 2., 3.
    fifth = f.deriv(5)/width**5
    sixth = f.deriv(6)/width**6
    def integral(fun):
        return quad(fun, middle-width, middle+width, epsabs=2e-11, epsrel=2e-11)[0]
    coeff = [integral(lambda t: .5*s.sol(t)[0]**2*sixth((t-middle)/width)) for s in sol]
    delta = integral(lambda t: fifth((t-middle)/width)*sol[0].sol(t)[1])
    assert abs(coeff[1]-coeff[0]-delta) < 2e-9 and abs(delta) > .01
    for idx, target in enumerate([.25, .75]):
        def drive(t, y, amp):
            z = (t-middle)/width
            e = amp*fifth(z) if abs(z)<1 else 0.
            return y[1], -y[0]*((y[0]-1)*(2*y[0]-1)+e)
        def end_energy(amp):
            end = solve_ivp(lambda t,y: drive(t,y,amp), [0,middle+width], [target,0],
                            method="DOP853", max_step=.045, rtol=2e-12, atol=1e-14).y[:, -1]
            r, v = end
            return .5*(v*v+(r*(r-1))**2)
        amp = 2e-7
        numerical = (end_energy(amp)-end_energy(-amp))/(2*amp)
        assert abs(numerical-coeff[idx]) < 9e-6
    return dict(preparations=read, extent_gap_min=float(min(gap)), later_work=coeff,
                work_difference=float(delta)), (times, lo, hi)


def orbit_stability():
    results = []
    for delta in [.25, .03, .005]:
        def maximum(t, y):
            return y[1]
        maximum.direction = -1
        orbit = solve_ivp(lambda t, y: [y[1], -y[0]*(y[0]-1)*(2*y[0]-1)],
                          [0, 10], [delta, 0], events=maximum, dense_output=True,
                          method="DOP853", rtol=2e-13, atol=2e-15)
        period = orbit.t_events[0][-1]
        assert 6 < period < 8
        first_harmonic = 2*quad(lambda t: orbit.sol(t)[0]*np.cos(2*pi*t/period),
                                 0., period, epsabs=2e-13)[0]/period
        for well in ["contracted", "expanded"]:
            # Two physical j=3 vector multiplets, independent of the Gauss directions.
            labels = np.array([3, -4])
            def ode(t, z):
                r = orbit.sol(t)[0]
                if well == "expanded":
                    r = 1-r
                frequency2 = (1+r*labels)**2+r*(1-r)*labels
                z = z.reshape(-1, 2, 2)
                return np.stack([z[:, 1], -frequency2[:, None]*z[:, 0]], axis=1).ravel()
            frames = solve_ivp(ode, [0, period], np.tile(np.eye(2), (2, 1, 1)).ravel(),
                               method="DOP853", rtol=2e-13, atol=2e-15).y[:, -1].reshape(-1, 2, 2)
            assert np.max(abs(np.linalg.det(frames)-1)) < 8e-12
            half = abs(np.trace(frames, axis1=1, axis2=2))/2
            exponents = np.arccosh(np.maximum(1., half))/period
            if well == "contracted":
                assert min(half) > 1
                if delta == .005:
                    coeff = np.sqrt(3.*(labels-2)*(labels+1)*(labels+2)*(labels+3))/2
                    assert np.max(abs(exponents/(first_harmonic**2*coeff)-1)) < .002
            results.append(dict(turning=delta, well=well, period=float(period),
                                fourier_amplitude=float(first_harmonic), exponents=exponents.tolist()))
    return results


def split_charges():
    def c(n):
        return n*(n*n-1)
    rows = []
    for n in range(2, 24):
        full = c(n)
        for m in range(1, n):
            loss = full-c(m)-c(n-m)
            assert loss == 3*n*m*(n-m)
            # Q=Casimir*a²/(2g²), instanton=Casimir*a³/(6g²), for a=g²=1.
            assert abs(loss/24-(loss/8)/3) < 1e-12
        rows.append([n, 3/(n+1)])
    return rows


def curvature_memory_checks():
    wells, trajectories = memory_paths()
    return dict(vertex=curvature_vertex(), chiral=chiral_matching(), spacelike=spacelike_insertions(),
                rotor=rotational_readout(),
                vector_hessians=[
                    matrix_hessian(n, r) for n, r in itertools.product([2, 4, 6], [.5, .75, .83, 1.])],
                bounce=[barrier_data(z) for z in [1., .9, .5, .1, .01, .001, .00001]],
                partition_fraction=split_charges(), supported_memory=wells, floquet=orbit_stability()), trajectories


def draw_curvature_memory(root, trajectories):
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.2, 3.0), layout="constrained")
    y = np.linspace(-.24, 1.19, 350)
    for h, style, color, label in [(0., "-", "#225868", "No extra tide"),
                                    (.10, "--", "#945728", r"$e/a^2=0.10$"),
                                    (.125, ":", "#463955", r"Loss of stability at $1/8$")]:
        left.plot(y, (y*y*((y-1)**2+h))/2, style, color=color, lw=1.7, label=label)
    left.set(xlabel=r"Membrane amplitude $r/a$", ylabel=r"Energy $V/(Ma^4)$", ylim=(-.006, .092))
    left.legend(fontsize=8, frameon=False)
    t, lo, hi = trajectories
    right.plot(t, hi**2, color="#225868", label="Expanded orbit")
    right.plot(t, lo**2, color="#945728", label="Contracted orbit")
    right.fill_between(t, lo**2, hi**2, color="#719d99", alpha=.12)
    right.set(xlabel=r"Time after the tide $a\,u$", ylabel=r"Tidal charge $2Q/(Ma^2)$", xlim=(0,24))
    right.legend(fontsize=8, frameon=False)
    for ax in (left,right):
        ax.spines[["right","top"]].set_visible(False)
    fig.savefig(root/"manuscripts/curvature_pair_memory.pdf", metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
