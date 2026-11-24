"""Internal work, joint matrix occupations and the width of an observer's layers.

All matrix lengths use the g_YM^2=1 BFSS normalization unless marked SZ.
The published radial density is for the largest singular value, not a single
matrix eigenvalue. Its sole numerical use below is a tail normalization check.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.linalg import expm

from layer_curvature_threshold import curvature_action_checks
from live_layer_gravity import live_layer_checks
from radiative_layer_selection import radiative_checks
from matrix_polarization_reference import reference_checks, draw_reference
from curvature_pair_memory import curvature_memory_checks, draw_curvature_memory
from gravitational_frame_flux import frame_flux_checks, draw_frame_flux
from matrix_contact_echo import matrix_contact_checks, draw_contact
from gravitational_recoil_records import recoil_records_checks, draw_recoil_records
from layer_response_spectrum import spectral_checks
from gravitational_exchange_write import exchange_write_checks

ROOT = Path(__file__).resolve().parents[1]
RAW = ROOT / "data/raw/su2-bfss-layer-response"
SQRT = math.sqrt


def generators(rank):
    """Tr(T_a T_b)=delta_ab. The center generator is omitted."""
    for i in range(rank):
        for j in range(i):
            real = np.zeros((rank, rank), dtype=complex)
            real[i, j] = real[j, i] = 1 / SQRT(2)
            yield real
            imag = np.zeros_like(real)
            imag[i, j], imag[j, i] = 1j / SQRT(2), -1j / SQRT(2)
            yield imag
    for j in range(1, rank):
        diagonal = [1.] * j + [-float(j)] + [0.] * (rank-j-1)
        yield np.diag(diagonal) / SQRT(j * (j+1))


def link_work():
    rng = np.random.default_rng(149)
    rows = []
    for rank, count in ((2, 1), (3, 2), (4, 5)):
        links = []
        for _ in range(count):
            z = rng.normal(size=(rank, rank)) + 1j*rng.normal(size=(rank, rank))
            q, r = np.linalg.qr(z)
            links.append(q @ np.diag(np.diag(r)/abs(np.diag(r))))

        def wilson(chain):
            out = np.eye(rank)
            for link in chain:
                out = out @ link
            return out

        def traces(chain):
            w = wilson(chain)
            return np.array([np.trace(w).real, np.trace(w @ w).imag])/rank

        theta = np.angle(np.linalg.eigvals(wilson(links)))
        slopes = np.array([-np.sin(theta), 2*np.cos(2*theta)])
        differences = slopes[:, :, None] - slopes[:, None, :]
        expected = np.einsum("iab,jab->ij", differences, differences)/(4*rank**3)
        numerical = np.zeros((2, 2))
        step = 2e-5
        for ell, link in enumerate(links):
            for gen in generators(rank):
                values = [traces(links[:ell]+[expm(sign*1j*step*gen) @ link]+links[ell+1:])
                          for sign in (1, -1)]
                grad = (values[0]-values[1])/(2*step)
                numerical += np.outer(grad, grad)/(2*count)
        error = float(abs(numerical-expected).max())
        assert error < 3e-10
        rows.append(dict(rank=rank, links=count, maximum_error=error))
    return rows


def compact_rotor():
    rows = []
    for n in (1, 2, 3, 7, 12):
        # SU(2) character orthogonality with Haar measure.
        coeffs = [quad(lambda a: 2/math.pi*math.sin(a)*math.sin((ell+1)*a)*
                       math.cos(n*a), 0, math.pi)[0] for ell in range(n+3)]
        elastic = sum(c*c for c in coeffs)
        relative = sum(ell*(ell+2)*c*c/4 for ell, c in enumerate(coeffs))
        assert abs(relative - n*n*(1-elastic)/4) < 1e-12
        rows.append(dict(n=n, static=elastic, spectral_work=relative))
    return rows


def singlet_moments():
    # SZ (D8, D9), BL Table 2, and an independent Rayleigh--Ritz calculation.
    tr2, potential, vtr2, determinant = 8.074210, 17.11246, 149.5830, 9.979125
    tr4, tr6 = 13.643*2**(4/3), 38.90*4
    m2 = 2*tr2/9
    m4 = (24*tr4-16*potential)/99
    m6 = (480*tr6-288*vtr2+192*determinant)/1287
    independent_m4 = (12*68.7529-16*potential)/99
    # Propagate quoted input widths by absolute interval arithmetic. Mixed
    # bootstrap envelopes and numerical errors do not give a confidence level.
    errors = [2*.000065/9, (24*.003*2**(4/3)+16*.000176)/99,
              (480*.01*4+288*.00086+192*.000108)/1287]
    assert abs(m4-independent_m4) < errors[1]+2e-5

    def band(k):
        lower = m2*k**4/16-m4*k**6/192
        upper = lower+m6*k**8/5760
        margin = errors[0]*k**4/16+errors[1]*k**6/192
        return [float(lower), float(upper), float(lower-margin),
                float(upper+margin+errors[2]*k**8/5760)]
    return dict(moments=[m2, m4, m6], propagated_input_widths=errors,
                independent_m4=independent_m4, quadrupole=tr2/18,
                quartic_coefficient=tr2/72,
                bands={str(k): band(k) for k in (.5, .8, 1.)})


def tail_checks():
    raw_file = RAW/"radial-profile.npz"
    raw_sha = hashlib.sha256(raw_file.read_bytes()).hexdigest()
    assert raw_sha == "6cec5dd68984691c67797e3b85da6657c8dcfc74317a0f98c85ac4c0d128dd36"
    with np.load(raw_file, allow_pickle=False) as data:
        rad, dens = data["R"], data["P"]
    norm = float(np.trapezoid(dens, rad))
    assert abs(norm-1) < 1e-5
    radial_tail = {str(r): float(np.interp(r, rad, dens*rad**10)) for r in (8, 10, 12)}
    angular = quad(lambda z: 35/16*z**9*(1-z*z)**3, 0, 1)[0]
    survival = 60480*angular/9
    assert abs(survival-105/4) < 1e-12

    def remainder_over_u10(u):
        if u < 3:
            return sum((-1)**j*u**(2*j)/math.factorial(10+2*j) for j in range(15))
        return (1-u*u/2+u**4/24-u**6/720+u**8/40320-math.cos(u))/u**10

    integral = quad(remainder_over_u10, 0, 3, epsabs=1e-17)[0]
    integral += quad(remainder_over_u10, 3, np.inf, epsabs=1e-14, limit=250)[0]
    coefficient = 9*survival*integral
    assert abs(coefficient-math.pi/3072) < 1e-12
    # Replace the whole core by either of two different point distributions.
    # Only the power-law tail and its mass agree. Compute the Taylor residual
    # without subtracting near-equal values of a numerically tabulated cosine.
    scan = []
    for k in (.5, .125, .03125, .0078125):
        omitted = quad(remainder_over_u10, 0, 2*k, epsabs=1e-16)[0]
        outer = 9*survival*(integral-omitted)
        at_one = outer + (1-survival/2**9)*k*remainder_over_u10(k)
        scan.append([k, outer, at_one])
    return dict(profile_sha256=raw_sha, profile_norm=norm, sz_tail=radial_tail,
                angular_ninth=angular, gap_survival=survival,
                characteristic_coefficient=coefficient, work_coefficient=coefficient/8,
                fitted_relative_amplitude=286.4/(893025/(32*math.pi**4)), distinct_cores=scan)


def observer_width():
    shapes = np.array([[0, 1, 4, 10, 12, 17], [0, 1, 8, 11, 13, 17]])
    differences = [sorted(b-a for a, b in itertools.combinations(shape, 2))
                   for shape in shapes]
    assert differences[0] == differences[1]
    phase = np.linspace(0, 2*math.pi, 2048, endpoint=False)
    form = np.exp(1j*math.pi*shapes/2)
    first, second = form.mean(axis=1), (form**2).mean(axis=1)
    triple = first**2 * second.conj()
    assert np.allclose(triple, [2j/27, -2j/27])
    outputs = []
    for z1, z2 in zip(first, second):
        x = (z1*np.exp(1j*phase)).real
        y = (z2*np.exp(1j*(2*phase+math.pi/2))).real
        assert abs((x*x*y).mean()-triple[len(outputs)].imag/4) < 1e-15
        outputs.append([float(np.mean(np.sin(2*e*x)**2*np.sin(2*e*y)))
                        for e in (.2, .1, .05)])
    parity = np.array(outputs)
    assert np.allclose(parity[0], -parity[1], atol=1e-15)
    eps = .05
    assert abs(parity[0,-1]/eps**3-4/27) < .0002
    gain = []
    for pa, pb in zip(*parity):
        prior_width = .25
        posterior_plus = (1+pa)/(2+pa+pb)
        posterior_minus = (1-pa)/(2-pa-pb)
        plus = (2+pa+pb)/4
        gain.append(prior_width-plus*posterior_plus*(1-posterior_plus)
                    -(1-plus)*posterior_minus*(1-posterior_minus))
    assert np.allclose(gain, parity[0]**2/4)
    # Binary Bayes reduction for a generally complex physical centroid.
    weights = np.array([.21, .35, .44])
    positions = np.array([-.7+.1j, .3+.2j, .9-.12j])
    signal = np.array([-.8, .35, .6])
    center = weights@positions
    orig = weights@abs(positions-center)**2
    remaining = 0.
    for sign in (-1, 1):
        joint = weights*(1+sign*signal)/2
        conditional = joint/joint.sum()
        remaining += joint.sum()*(conditional@abs(positions-conditional@positions)**2)
    analytic = abs(weights@((positions-center)*signal))**2/(1-(weights@signal)**2)
    assert abs(orig-remaining-analytic) < 1e-14
    return dict(separations=list(map(int, differences[0])), bispectrum_imaginary=triple.imag.tolist(),
                strengths=[.2,.1,.05], parity=parity.tolist(), thickness_loss=gain,
                bayes_width_reduction=analytic)


def differential_gravity():
    """Compare a curvature-only force with the information carried through gravity."""
    from scipy.integrate import solve_ivp
    from scipy.special import sici
    mass, kappa, contrast = 1.4, .37, .06
    horizon = 2*mass
    radial = horizon*np.array([1.0001, 1.1, 2., 5., 10., 35.])
    charge = 4*kappa*contrast/mass**2

    def profile(radius):
        return charge*(1/radius + mass/radius**2 + 4*mass**2/(3*radius**3))

    # Integrate the source from the regular horizon, then integrate the flux
    # inward from infinity. The source quadrature remains regular at its lower limit.
    def flux_per_area(radius):
        inward = quad(lambda r: 96*kappa*mass*contrast/r**4, horizon, radius)[0]
        return inward/(radius*(radius-horizon))

    direct = [quad(flux_per_area, r, np.inf, epsabs=3e-12)[0] for r in radial]
    assert np.allclose(direct, profile(radial), rtol=1e-10)
    horizon_value = charge*11/(12*mass)
    assert abs(profile(horizon)-horizon_value) < 1e-14
    # The same ODE as a first-order flux evolution away from r=2M.
    flight = solve_ivp(lambda r,state: [-96*kappa*mass*contrast/r**4],
                       (horizon, radial[-1]), [0.], t_eval=radial, rtol=1e-10, atol=1e-12)
    assert flight.success
    assert np.max(np.abs(flight.y[0]-32*kappa*mass*contrast*(radial**-3-horizon**-3))) < 5e-11

    omega = np.array([.45, 1.2, 3.1])
    source = np.array([.31, .27, .44])
    mixing = np.array([[.15, .68, 0.], [.36, .04, .5]])
    assert np.all(mixing.sum(axis=0) <= 1)
    # Direct quadrature to a finite time plus a sine-integral tail.
    time_end = 120.
    def single_area(w):
        val = quad(lambda t: 2*(math.sin(w*t/2)/t)**2, 0., time_end,
                   epsabs=2e-11, limit=240)[0]
        tail = (1-math.cos(w*time_end))/time_end + w*(math.pi/2-sici(w*time_end)[0])
        return val+tail
    areas = np.array([single_area(w) for w in omega])/omega**2
    measured = float(np.dot(source**2, areas))
    static = float(np.dot(source**2, 1/omega))
    assert math.isclose(measured, math.pi*static/2, abs_tol=3e-12)
    local = (mixing@(source**2*areas)).tolist()
    assert sum(local) < measured
    # Sum the actual marked Poisson probabilities for both material channels.
    p, q, flux = np.array([.77, .23]), np.array([.21, .79]), 3.4
    weights = np.sqrt(p*q)
    record_overlap = 0.
    for a in range(35):
        for b in range(35):
            record_overlap += (math.exp(-flux)*(flux*weights[0])**a/math.factorial(a)
                               *(flux*weights[1])**b/math.factorial(b))
    assert abs(record_overlap-math.exp(-flux*(1-weights.sum()))) < 1e-14
    return dict(horizon_scaled_radius=(radial/horizon).tolist(),
                relative_scalar=direct, horizon_limit=horizon_value, field_charge=charge,
                k3_relative_coefficient=-48/96, schwarzschild_odd_source=0,
                relative_binding=static, integrated_field_capacity=measured,
                passive_received_capacities=local, poisson_affinity=record_overlap)


def discrete_euler_source():
    """Euler curvature measure on the four-manifold S^2 x S^2.

    Only edge lengths and triangle incidences enter the curvature. The round
    embedding supplies the preparation and a fixed physical comparison scalar.
    """
    from scipy.spatial import ConvexHull
    phi = (1+SQRT(5))/2
    vertices = np.array([np.roll([0., a, b*phi], shift) for a in (-1,1)
                         for b in (-1,1) for shift in range(3)])
    vertices = vertices/np.linalg.norm(vertices, axis=1)[:,None]
    faces = ConvexHull(vertices).simplices
    amplitude = .08
    history = []
    for depth in range(6):
        y = (3*vertices[:,2]**2-1)/2
        values = []
        for sign in (-1,1):
            opposite = []
            for j in range(3):
                s, t = faces[:,(j+1)%3], faces[:,(j+2)%3]
                ordinary = np.linalg.norm(vertices[s]-vertices[t], axis=1)
                opposite.append(ordinary*np.exp(sign*amplitude*(y[s]+y[t])/2))
            deficit = np.full(len(vertices), 2*math.pi)
            for j,(s,t,u) in enumerate([(0,1,2),(1,2,0),(2,0,1)]):
                a, b, c = opposite[s],opposite[t],opposite[u]
                cosine = (b*b+c*c-a*a)/(2*b*c)
                assert np.all(abs(cosine) < 1)
                np.add.at(deficit, faces[:,j], -np.arccos(cosine))
            total = float(deficit.sum())
            assert math.isclose(total, 4*math.pi, abs_tol=2e-10)
            values.append(float(np.dot(y, deficit)/math.pi))
        relative = (values[1]-values[0])/2
        history.append(dict(vertices=len(vertices), faces=len(faces), contrast=relative,
                            absolute_error=abs(relative-24*amplitude/5)))
        if depth < 5:
            # Deduplication makes neighboring triangles share exactly one vertex.
            edges = np.vstack([faces[:,[0,1]], faces[:,[1,2]], faces[:,[2,0]]])
            unique, back = np.unique(np.sort(edges,axis=1),axis=0,return_inverse=True)
            mid = vertices[unique[:,0]]+vertices[unique[:,1]]
            mid = mid/np.linalg.norm(mid,axis=1)[:,None]
            ab,bc,ca = (back.reshape(3,-1)+len(vertices))
            a,b,c = faces.T
            faces = np.vstack([np.stack(tri,axis=1) for tri in
                               ((a,ab,ca),(ab,b,bc),(ca,bc,c),(ab,bc,ca))])
            vertices = np.vstack((vertices,mid))
    errors = [row["absolute_error"] for row in history]
    assert all(later < earlier for earlier,later in zip(errors,errors[1:]))
    assert errors[-1] < .0005
    return dict(amplitude=amplitude, limit=24*amplitude/5, uniform_euler_charge=4,
                refinement=history)


def axial_layer_transfer():
    """Schwarzschild transfer from an ordinary metric packet to its layer complement.

    The same radial solver used in paper II supplies the massless, odd-parity
    blocks. Here its ports are embedded in a common metric and a relative
    metric/scalar sector. Both the exterior and the horizon carry flux.
    """
    from reciprocal_gravity_records import scattering

    metric_ports = [0, 2]
    relative_indices = [1, 2, 4, 5]
    common_indices = [0, 3]
    layer_rotation = np.array([[1, 1, 0], [1, -1, 0], [0, 0, SQRT(2)]])/SQRT(2)
    rotation = np.kron(np.eye(2), layer_rotation)
    rows = []
    for frequency, strength in ((.25, .9), (.36, .45), (.36, .9), (.36, 1.8), (.50, .9)):
        estimates = []
        for refined in (False, True):
            # strength is 24 sqrt(pi) alpha/(sqrt(beta) M^2); the radial
            # routine's coupling is defined with an off-diagonal factor of 6.
            ordinary = scattering(frequency, 0., refined=refined)
            common = ordinary[np.ix_(metric_ports, metric_ports)]
            contrast = scattering(frequency, strength/6, refined=refined)
            channels = np.zeros((6, 6), complex)
            channels[np.ix_(common_indices, common_indices)] = common
            channels[np.ix_(relative_indices, relative_indices)] = contrast
            physical = rotation @ channels @ rotation.T
            plus = (physical[:, 0]+physical[:, 1])/SQRT(2)
            minus = (physical[:, 0]-physical[:, 1])/SQRT(2)
            assert np.linalg.norm(plus[[2, 5]]) < 1e-14
            emitted = abs(minus[[2, 5]])**2
            transferred = abs(physical[[1, 4], 0])**2
            assert np.max(abs(2*abs(physical[[2, 5], 0])**2-emitted)) < 1e-14
            assert np.max(abs(physical.conj().T @ physical-np.eye(6))) < 1e-8
            assert np.max(abs(physical-physical.T)) < 1e-8
            probability = float(emitted.sum())
            lower_bound = .25*(probability/(1+SQRT(1-probability)))**2
            assert transferred.sum()+1e-14 >= lower_bound > 0
            estimates.append(np.array([*emitted, *transferred, lower_bound]))
        error = np.max(abs(estimates[1]-estimates[0]))
        assert error < 1e-7
        exterior_b, horizon_b, exterior_g, horizon_g, bound = estimates[1]
        rows.append(dict(omega_mass=frequency, dimensionless_strength=strength,
                         differential_to_scalar_exterior=exterior_b,
                         differential_to_scalar_horizon=horizon_b,
                         first_to_second_metric_exterior=exterior_g,
                         first_to_second_metric_horizon=horizon_g,
                         metric_transfer_lower_bound=bound, boundary_check=error))
    # A ratio of two weak-conversion signals eliminates the unknown coupling.
    # Richardson extrapolation in strength squared uses three nested pairs.
    frequency = .36
    common = scattering(frequency, 0., refined=True)[metric_ports, 0]
    small = []
    for strength in (.225, .1125, .05625, .028125):
        relative = scattering(frequency, strength/6, refined=True)
        converted = float(np.sum(abs(relative[[1, 3], 0])**2))
        other_metric = float(np.sum(abs(common-relative[metric_ports, 0])**2)/4)
        small.append(dict(strength=strength, scalar_per_strength2=converted/strength**2,
                          metric_per_strength4=other_metric/strength**4,
                          ratio=other_metric/converted**2))
    extrapolated = [(4*r["ratio"]-s["ratio"])/3 for s, r in zip(small, small[1:])]
    assert abs(extrapolated[-1]-extrapolated[-2]) < 3e-7
    assert extrapolated[-1] > 1/16
    # The response to writing a perfectly common input follows independently
    # from a density matrix in the two localized profiles.
    marks = []
    for weight, visibility in ((.5, 1.), (.5, .25), (.2, .4)):
        contrast_packet = np.array([SQRT(1-weight), -SQRT(weight)])
        common_packet = np.array([SQRT(weight), SQRT(1-weight)])
        marked = np.outer(common_packet, common_packet)
        marked[0, 1] *= visibility
        marked[1, 0] *= visibility
        occupation = float(contrast_packet @ marked @ contrast_packet)
        assert abs(occupation-2*weight*(1-weight)*(1-visibility)) < 2e-15
        marks.append(dict(support=weight, retained_visibility=visibility,
                          differential_occupation=occupation))
    return dict(radial=rows, small_coupling=small, extrapolated_ratio=extrapolated,
                early_layer_selection=marks)


def draw_curvature():
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(8.4, 3.2), layout="constrained")
    radius = np.linspace(1, 6, 240)
    shape = (1/(2*radius)+1/(4*radius**2)+1/(6*radius**3))/(11/12)
    ax.plot(radius, shape, color="#225e73", label="Even curvature source")
    ax.plot(radius, 0*radius, color="#a95c28", ls="--", label="Odd curvature source")
    ax.set(xlabel=r"Areal radius $r/(2M)$", ylabel="Response / even horizon value",
           title="Static mass contrast")
    ax.legend(frameon=False, fontsize=8)
    delta = np.linspace(-np.pi, np.pi, 240)
    bx.plot(delta/np.pi, np.cos(delta), color="#225e73", label="Internal charge 1")
    bx.plot(delta/np.pi, np.cos(2*delta), color="#a95c28", label="Internal charge 2")
    bx.axhline(0, lw=.6, color="0.6")
    bx.set(xlabel=r"Layer separation $(\ell-\ell')/\pi$", ylabel="Normalized exchange kernel",
           title="No uniform-source component")
    bx.legend(frameon=False, fontsize=8)
    for axis in (ax,bx):
        axis.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts/layer_curvature_response.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def draw(data):
    k = np.linspace(0, 1.1, 200)
    m2, m4, m6 = data["bound_state"]["moments"]
    low = m2/16-m4*k**2/192
    high = low+m6*k**4/5760
    fig, axes = plt.subplots(1, 2, figsize=(8.4, 3.2), layout="constrained")
    axes[0].fill_between(k, low, high, color="#8bbcd0")
    axes[0].plot(k, low, color="#235169", lw=1.4)
    axes[0].plot(k, high, color="#235169", lw=1.4)
    axes[0].set(xlabel=r"Matrix wave number $k$", ylabel=r"Internal work $m(k)/k^4$",
                title="Bound state of two D0-branes")
    phase = np.linspace(0, 2*math.pi, 400)
    for shape, color, label in [([0,1,4,10,12,17], "#235169", "Shape A"),
                                ([0,1,8,11,13,17], "#ad591e", "Shape B")]:
        second = np.exp(1j*math.pi*np.array(shape)).mean()
        axes[1].plot(phase/(2*math.pi), (second*np.exp(1j*(2*phase+math.pi/2))).real,
                     color=color, label=label)
    axes[1].set(xlabel="Translation in periods of the first mode",
                ylabel="Second-mode quadrature", title="Shapes with identical pair statistics")
    axes[1].legend(frameon=False, ncol=2, fontsize=8, loc="upper center")
    for ax in axes:
        ax.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts/matrix_layer_work.pdf",
                metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def draw_collapse(data):
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.5, 3.2), layout="constrained")
    sectors = data["compact_collapsing_data"][0]["sectors"]
    for model, color, label in zip(sectors, ["#235169", "#aa5421"], ["Zero scalar", "Occupied scalar"]):
        left.plot(model["radii"], model["compactness"], color=color, label=label)
    left.axhline(1., color=".4", ls=":", lw=1)
    left.set(xlabel="Areal radius on the initial slice", ylabel=r"$2Gm(r)/r$",
             title="A trapped region with a vacuum exterior", xlim=(0, 40), ylim=(0, None))
    left.legend(frameon=False, fontsize=8)
    for curve, color, label in zip(data["evolution_curves"], ["#235169", "#aa5421"], ["Expansion", "Contraction"]):
        right.plot(curve["proper_times"], curve["scaled_curvature"], color=color, label=label)
    right.set(xlabel=r"Receiver proper time $\tau$", ylabel=r"$\Delta R/\tau^2$",
              title="Curvature in the receiving layer")
    right.legend(frameon=False, fontsize=8)
    for axis in (left, right):
        axis.spines[["top", "right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts/live_layer_gravity.pdf", metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


def draw_radiation(data):
    fig, (left, right) = plt.subplots(1, 2, figsize=(8.5, 3.3), layout="constrained")
    colors = ["#244f68", "#a55624", "#59804b"]
    for row, color in zip(data["visibility_curves"], colors):
        left.loglog(row["times"], row["losses"], color=color, label=rf"$1-v^2={row['missing']:g}$")
    left.set(xlabel=r"Tidal exposure $B^{1/6}T$", ylabel=r"Squared fidelity deficit $1-\mathcal{F}^2$",
             title="Information in two scattered beams")
    left.legend(frameon=False, fontsize=8)
    for row, color in zip(data["circle"], colors):
        right.semilogx(row["radii"], row["exponent"], "o-", ms=3, color=color,
                       label=rf"$z={row['scaling']:g}$")
        right.axhline(row["limit"], linestyle=":", lw=.9, color=color)
    right.set(xlabel=r"Size of the circle $R\Lambda$", ylabel=r"Soft integral $I_R/\Lambda$",
              title="Radiation into an opening circle")
    right.legend(frameon=False, fontsize=8)
    for axis in (left, right):
        axis.spines[["top", "right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts/radiative_layer_selection.pdf", metadata={"CreationDate": None, "ModDate": None})
    plt.close(fig)


if __name__ == "__main__":
    pair_memory, trajectories = curvature_memory_checks()
    data = dict(links=link_work(), compact=compact_rotor(), bound_state=singlet_moments(),
                tail=tail_checks(), observers=observer_width(), differential=differential_gravity(),
                refined_curvature=discrete_euler_source(), axial_transfer=axial_layer_transfer(),
                action_candidates=curvature_action_checks(), coupled_evolution=live_layer_checks(),
                gravitational_write=exchange_write_checks(), radiative_selection=radiative_checks(),
                layer_spectrum=spectral_checks(), polarization_reference=reference_checks(),
                curvature_pair_memory=pair_memory, gravitational_frame=frame_flux_checks(),
                matrix_contact=matrix_contact_checks(), recoil_records=recoil_records_checks())
    draw(data)
    draw_curvature()
    draw_radiation(data['radiative_selection'])
    draw_reference(ROOT)
    draw_curvature_memory(ROOT, trajectories)
    draw_frame_flux(ROOT, data['gravitational_frame'])
    draw_collapse(data['coupled_evolution'])
    draw_contact(ROOT, data['matrix_contact'])
    draw_recoil_records(ROOT)
    (ROOT/"verification/matrix-layer-work-results.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print("Matrix work, SU(2) rotor, published SU(2) profile, and conditional layer widths checked.")
