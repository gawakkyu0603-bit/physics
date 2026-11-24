"""Coherent compact-momentum returns from the leading D2/M2 eikonal action.

The FFT solves the circle problem. Exponentiating a real symmetric channel
Hamiltonian is a separate calculation at fixed total scattering energy.
"""
import json
import math
import os
from pathlib import Path

for variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[variable] = "1"
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.linalg import eigh, toeplitz
from scipy.special import i0e, j0, kv

ROOT = Path(__file__).resolve().parents[1]


def weights(z, maximum):
    x = z * np.arange(1, maximum + 1, dtype=float)
    return 0.5 * x**2 * kv(2, x)


def circle(z, u, size=4096):
    # All Fourier coefficients use the normalized Haar measure on the circle.
    k = np.arange(1, 49)
    angles = 2 * np.pi * np.arange(size) / size
    f = weights(z, k.size)
    eps = u / (4 * f[0])
    cosines = np.cos(np.outer(k, angles))
    phase = 2 * eps * (f @ cosines)
    phase_prime = -2 * eps * ((k*f) @ np.sin(np.outer(k, angles)))
    phase_second = -2 * eps * ((k**2*f) @ cosines)
    pulse = np.exp(1j * phase)
    transfer = np.fft.fft(pulse)/size
    charge = np.rint(np.fft.fftfreq(size)*size).astype(int)
    parity = (-1.)**charge
    probability = abs(transfer)**2
    shifted = np.roll(pulse, size//2)
    h = pulse/shifted
    h_power = abs(np.fft.fft(h)/size)**2
    c = float(parity @ probability)
    assert abs(1-sum(probability)) < 1e-13 and abs(c-np.mean(h)) < 1e-13
    # A completely distinct implementation projects the first wave onto each
    # residue, propagates that branch and sums final probabilities incoherently.
    cases = {}
    for d in (1, 2, 3, 4, 6, 8, 0):
        keep = charge == 0 if d == 0 else (charge % d == 0)
        odd = (1-float(h_power[keep].sum()))/2
        if d:
            direct = 0.
            for r in range(d):
                first = transfer * ((charge % d) == r) * parity
                final = np.fft.fft(pulse*np.fft.ifft(first*size))/size
                direct += float(np.sum(abs(final[parity < 0])**2))
        else:
            # Complete charge information leaves two independent Born outcomes.
            direct = 2*probability[parity < 0].sum()*probability[parity > 0].sum()
        assert abs(odd-direct) < 2e-13
        cases[str(d)] = float(direct)
    assert abs(cases["2"] - (1-float(np.mean((h**2).real)))/4) < 1e-13
    m2 = float(probability @ charge**2)
    m4 = float(probability @ charge.astype(float)**4)
    assert abs(m2-np.mean(phase_prime**2)) < 1e-12
    assert abs(m4-np.mean(phase_second**2 + phase_prime**4)) < 1e-10
    dtheta, dbeta = .01, -.004
    early = transfer*parity*np.exp(1j*dtheta*charge - 1j*dbeta*charge**2)
    late = np.fft.fft(pulse*np.fft.ifft(size*early))/size
    mistimed = float((abs(late[parity < 0])**2).sum())
    bound = (abs(dtheta)*math.sqrt(m2) + abs(dbeta)*math.sqrt(m4))**2
    assert mistimed <= bound
    return dict(impact_over_radius=z, scaled_strength=u, strength=eps,
                elastic=float(probability[0]), parity=c, odd=(1-c)/2,
                twice_strength_parity=float(np.mean((h**2).real)),
                odd_after_two=cases, second_moment=m2, fourth_moment=m4,
                timing=dict(angle=dtheta, recoil_phase=dbeta, odd=mistimed, upper=bound))


def fixed_energy(z, eps, cutoff):
    ks = np.arange(-cutoff, cutoff+1)
    profile = weights(z, 2*cutoff)
    generator = toeplitz(np.r_[0., profile])
    center = cutoff
    parity = (-1.)**ks
    vals, vecs = eigh(generator)
    pulse = (vecs*np.exp(1j*eps*vals)) @ vecs.T
    first = pulse[:, center]
    two = pulse @ (parity*first)
    commutator = pulse @ (parity[:, None]*pulse*parity[None, :])
    diff = commutator - commutator.T
    odd = float(np.linalg.norm(two[parity < 0])**2)
    assert abs(odd - float(np.linalg.norm(diff[:,center])**2)/4) < 1e-14
    intermediate_parity = 0.
    for sign in (1, -1):
        marked = pulse @ (first * (parity==sign) * parity)
        intermediate_parity += float(np.linalg.norm(marked[parity<0])**2)
    # Bound infinite weighted norm with a geometric majorant including its tail.
    sigma = .5
    def majorant(exponent):
        r = math.exp(-z+exponent)
        return 2*profile[0]*math.exp(exponent)*(1+r)/(1-r)**3
    bound = math.exp(-sigma*(cutoff+1) + 2*abs(eps)*majorant(sigma))
    bound *= 1+2*abs(eps)*majorant(0.)
    return dict(open_half_width=cutoff, inclusive_parity=float(parity @ abs(first)**2),
                odd_without_mark=odd, odd_with_parity_mark=intermediate_parity,
                two_pass_state_error_bound=bound)


def charge_constraints():
    # Compute the actual components on a cyclic test lattice, rather than
    # assuming the Bezout formula. Integer examples include exact reception.
    size = 120
    examples = []
    for d, shifts in ((0,[1]), (0,[2,4]), (12,[6,9]), (6,[4]), (0,[])):
        adjacency = shifts + ([d] if d else [])
        remaining = set(range(size))
        parts = []
        while remaining:
            front = [min(remaining)]
            seen = set(front)
            while front:
                index = front.pop()
                for jump in adjacency:
                    for sign in (-1, 1):
                        neighbor = (index+sign*jump) % size
                        if neighbor not in seen:
                            seen.add(neighbor)
                            front.append(neighbor)
            parts.append(seen)
            remaining.difference_update(seen)
        modulus = math.gcd(size, d, *shifts)
        assert len(parts)==modulus and all(len({x%modulus for x in s})==1 for s in parts)
        examples.append(dict(received_modulus=d,transfer_steps=shifts,cyclic_components=len(parts)))
    column = np.array([[4, 0, -9], [-4, 6, 0], [0, -6, 9]])
    assert np.all(column.sum(axis=0)==0) and np.all((np.array([0,3,2])@column)%6==0)
    # Relative lattice index is the gcd of maximal minors in primitive total-zero coordinates.
    relative = column[1:,:]
    def index(generators):
        minors = [int(generators[0,i]*generators[1,j]-generators[1,i]*generators[0,j])
                  for j in range(generators.shape[1]) for i in range(j)]
        return math.gcd(*minors)
    assert index(relative)==6 and index(np.column_stack((relative,[1,-1])))==1
    return dict(two_clusters=examples,three_cluster_torsion=6,with_unit_23=1)


def state_dependent_writes():
    coupling = 1.
    eigen = np.eye(2, dtype=complex)
    coherent = np.array([[1,1j],[1,-1j]])/math.sqrt(2)
    def decomposition(states):
        rho = sum(np.outer(v,v.conj()) for v in states)/len(states)
        rate = np.mean([abs(2*coupling*(v[1].conj()*v[0]).imag) for v in states])
        return rho, float(rate)
    a, ra = decomposition(eigen)
    b, rb = decomposition(coherent)
    assert np.allclose(a,b) and abs(ra)<1e-14 and abs(rb-1)<1e-14
    return dict(charge_preparation_rate=ra,phase_preparation_rate=rb,
                one_way_parity_after_two_lifetimes=float(2*np.exp(-2)-1))


def flight_winding(z, case):
    carrier, long_momentum = 4096, 1e8
    eps = case["strength"]
    n = 4096
    phi = 2*np.pi*np.arange(n)/n
    h = np.arange(1,49)
    x = h*z
    f = weights(z,len(h))
    pulse = np.exp(2j*eps*(f@np.cos(np.outer(h,phi))))
    changes = np.rint(np.fft.fftfreq(n)*n).astype(int)
    first = np.fft.fft(pulse)/n
    extra = np.pi/(2*carrier)
    delayed = first*((-1.)**changes)*np.exp(-1j*extra*changes**2)
    second=np.fft.fft(pulse*np.fft.ifft(n*delayed))/n
    odd=float(np.sum(abs(second[changes%2==1])**2))
    upper=extra**2*case["fourth_moment"]
    assert odd<=upper
    # The common forward force also changes the next impact parameter.
    gradient=abs(eps)*(4+2*np.sum(4*f+x**3*kv(1,x)/2))
    return dict(carrier=carrier,longitudinal_momentum_times_radius=long_momentum,
                circumference_over_impact=math.pi*long_momentum/(carrier*z),
                compact_drift_during_encounter=carrier*z/long_momentum,
                recoil_only_odd=odd,recoil_only_bound=upper,
                impact_drift_fraction_bound=math.pi*gradient/(carrier*z**2),
                diffraction_scale=math.sqrt(math.pi/carrier)/z)


def field_returns(z, eps):
    # Two encounters use the same quantized oscillator; a second check evolves
    # its truncated number basis at each angle and traces it only at the end.
    angles = 2*np.pi*np.arange(192)/192
    k = np.arange(1,31)
    phase = 2*eps*(weights(z,30) @ np.cos(np.outer(k,angles)))
    amplitude = .65
    drive = amplitude*np.cos(angles)
    ladder = np.diag(np.sqrt(np.arange(1,24)),1)
    eigenvalues, vectors = eigh(1j*(ladder.T-ladder))
    turns = np.exp(-1j*np.outer(drive,eigenvalues))
    vacuum = np.eye(24)[0]
    def kick(states):
        return (turns*(states@vectors.conj()))@vectors.T
    first = np.exp(1j*phase)[:,None]*kick(np.broadcast_to(vacuum,(len(angles),24)))
    rows = []
    for t in (0., .5*np.pi, np.pi, 2*np.pi):
        s = np.exp(-1j*t)
        free = np.exp(-1j*t*np.arange(24))
        def final_odd(early):
            out = np.exp(1j*phase)[:,None]*kick(early*free)
            odd_component = (out - np.roll(out,len(angles)//2,axis=0))/2
            return float(np.mean(np.sum(abs(odd_component)**2,axis=1)))
        p_return = final_odd(np.roll(first,len(angles)//2,axis=0))
        p_plain = final_odd(first)
        xi = amplitude**2 * abs(1-s)**2
        assert abs(p_return-(1-i0e(xi))/2)<2e-13
        plain_parity = np.mean(np.cos(2*(phase-np.roll(phase,len(angles)//2)))
                               *np.exp(-2*drive**2*abs(1+s)**2))
        assert abs(p_plain-(1-plain_parity)/2)<2e-13
        q=.37
        p_mixed=(1-q/2)*p_return+(q/2)*p_plain
        restored=2*(p_mixed-p_return)/(p_plain-p_return)
        assert abs(restored-q)<2e-14
        rows.append(dict(field_angle=t, displacement_spectrum=xi, coherent_odd=p_return,
                         unshifted_odd=p_plain, assumed_fraction=q, mixed_odd=p_mixed))
    fresh=(1-i0e(2*amplitude**2))/2
    return dict(displacement=amplitude, independent_field_odd=float(fresh), same_field=rows)


def soft_records():
    # Unit ultraviolet scale and unit product of the Ohmic strength with
    # squared source contrast. Recoil energy is in units of that scale.
    rows = []
    for t in (.25,1.,4.,16.):
        def loss(w):
            return math.exp(-w)*2*math.sin(w*t/2)**2
        variance = quad(lambda w: loss(w)/w,0.,80.,epsabs=2e-12,epsrel=2e-13,limit=500)[0]
        energy = 2*quad(loss,0.,80.,epsabs=2e-12,epsrel=2e-13,limit=500)[0]
        assert abs(variance - .5*math.log1p(t*t)) < 2e-11
        assert abs(energy - 2*t*t/(1+t*t)) < 2e-10
        rows.append(dict(hold_time=t,overlap=math.exp(-variance),difference_energy=energy))
    return dict(ohmic=rows,tidal_exponents={str(d):d+1 for d in (4,10,11)})


def terminal_receiver(z, strength):
    # One internal transition that absorbs the relative motion into a
    # distinguishable bound channel. Energy and momentum go to the sink and
    # to a neutral zero-mode graviton. The benchmark holds the reduced
    # quadrupole form factor fixed, after removing the fifth power of energy.
    n = 4096
    k = np.rint(np.fft.fftfreq(n)*n).astype(int)
    phi = np.arange(n)*2*np.pi/n
    harmonics = np.arange(1,49)
    pulse = np.exp(2j*strength*(weights(z,48)@np.cos(np.outer(harmonics,phi))))
    first = np.fft.fft(pulse)/n
    p = abs(first)**2
    parity = (-1.)**k
    rows=[]
    for mr in (2.,5.,20.):
        omega_ratio = 1/np.sqrt(1+(k/mr)**2)
        # Check exact zero-KK two-body energies in units R=1.
        parent=np.hypot(mr,k)
        daughter=np.hypot(.95*mr,k)
        omega0=(mr**2-(.95*mr)**2)/(2*mr)
        omega=omega_ratio*omega0
        assert np.max(abs(parent-np.hypot(daughter,omega)-omega))<6e-13
        for exposure in (.4,1.,2.):
            width=omega_ratio**5
            survival=np.exp(-width*exposure/2)
            caught=p*(-np.expm1(-width*exposure))
            returned=np.fft.fft(pulse*np.fft.ifft(n*survival*first*parity))/n
            joint_odd=float(np.sum(abs(returned[parity<0])**2))
            pass_prob=float(p@survival**2)
            # Center before squaring so the variance stays accurate for large masses.
            upper=float(p@(survival-float(p@survival))**2)
            assert abs(pass_prob+caught.sum()-1)<2e-14
            assert joint_odd<=upper+1e-15
            rows.append(dict(parent_mass_times_radius=mr,exposure_in_rest_lifetimes=exposure,
                             probability_caught=float(caught.sum()), odd_and_survived=joint_odd,
                             variance_upper=upper, odd_given_caught=float(caught[parity<0].sum()/caught.sum())))
    return rows


def receiver_orientation(z, strength):
    size=4096
    phi=2*np.pi*np.arange(size)/size
    harmonics=np.arange(1,49)
    phase=2*strength*(weights(z,48)@np.cos(np.outer(harmonics,phi)))
    p=abs(np.fft.fft(np.exp(1j*phase))/size)**2
    k=np.rint(np.fft.fftfreq(size)*size).astype(int)
    width=(1+(k/5.)**2)**(-2.5)
    captured=p*(-np.expm1(-width))
    captured/=captured.sum()
    choices=[]
    for d in (1,2,3,4,6,8):
        paths=np.arange(d)
        check_k=np.arange(0,3*d+1)
        moments=np.mean(np.exp(2j*np.pi*check_k[:,None]*paths/d),axis=1)
        assert np.allclose(moments,(check_k%d)==0,atol=2e-14)
        gram=np.exp(2j*np.pi*np.outer(paths,paths)/d)/math.sqrt(d)
        assert np.linalg.norm(gram.conj().T@gram-np.eye(d))<2e-14
        ambiguous=float(captured[(k!=0)&(k%d==0)].sum())
        choices.append(dict(paths=d,undecidable_sign_mass=ambiguous,
                            error_given_magnitude=ambiguous/2))
    # Two equal arms, with magnitudes one and two presented individually.
    theta=np.linspace(0,np.pi,6001)
    guessing=(1+np.minimum(abs(np.sin(theta)),abs(np.sin(2*theta))))/2
    unambiguous=1-np.maximum(abs(np.cos(theta)),abs(np.cos(2*theta)))
    assert abs(guessing.max()-(2+math.sqrt(3))/4)<1e-14
    assert abs(unambiguous.max()-.5)<1e-14
    return dict(conditional_rest_charge=float(captured[0]),regular_receivers=choices,
                two_paths_worst_case_guess=float(guessing.max()),
                two_paths_worst_case_conclusive=float(unambiguous.max()))


def draw(z, reference):
    strengths = np.linspace(0,9,280)
    angles = 2*np.pi*np.arange(2048)/2048
    k = np.arange(1,49,2)
    f = weights(z,48)
    shape = (f[k-1] @ np.cos(np.outer(k,angles)))/f[0]
    phase = strengths[:,None]*shape
    c = np.cos(phase).mean(axis=1)
    parity_mark = (1-np.cos(2*phase).mean(axis=1))/4
    fig, ax = plt.subplots(1,2,figsize=(8.45,3.25),layout="constrained")
    ax[0].axhline(0,color=".58",lw=.8)
    ax[0].fill_between(strengths,-1,0,color="#eed8c0",alpha=.45)
    ax[0].plot(strengths,c,color="#275b77",label="All compact transfers")
    ax[0].plot([4],[reference["parity"]],"o",color="#a65027")
    ax[0].set(xlabel=r"One-pass phase $4\epsilon F(z)$",ylabel=r"Average charge parity",ylim=(-.6,1.08))
    ax[1].plot(strengths,(1-c**2)/2,label="Whole charge recorded",color="#a65027")
    ax[1].plot(strengths,parity_mark,label="Parity recorded",color="#275b77")
    ax[1].axhline(0,color=".28",ls="--",label="Coherent return")
    ax[1].set(xlabel=r"One-pass phase $4\epsilon F(z)$",ylabel="Odd probability after two passes",ylim=(-.022,.54))
    for a in ax:
        a.grid(alpha=.18)
        a.legend(fontsize=8,frameon=False)
    out=ROOT/"manuscripts"/"coherent_gravity_returns.pdf"
    out.parent.mkdir(exist_ok=True)
    fig.savefig(out,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    z, u = math.log(32),4.
    reference = circle(z,u)
    fine = circle(z,u,8192)
    assert abs(fine["parity"]-reference["parity"])<2e-14
    bound = 36/1015
    assert abs(reference["parity"]-j0(4)) <= bound and reference["parity"] < -.25
    energies = [fixed_energy(z,reference["strength"],cut) for cut in (2,4,8,16,32,64)]
    assert abs(reference["parity"]-energies[-1]["inclusive_parity"])<2e-13
    assert abs(reference["odd_after_two"]["2"]-energies[-1]["odd_with_parity_mark"])<2e-13
    assert energies[-1]["two_pass_state_error_bound"] < 1e-7
    result = dict(circle=reference, first_harmonic_parity=float(j0(4)),
                  certified_tail=bound,energy_fibres=energies,charges=charge_constraints(),
                  local_rate_test=state_dependent_writes(),
                  mediator=field_returns(z, reference["strength"]), soft=soft_records(),
                  terminal=terminal_receiver(z,reference["strength"]), winding=flight_winding(z,reference),
                  orientation=receiver_orientation(z,reference["strength"]))
    out = ROOT/"verification"/"coherent-gravity-returns-results.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    draw(z,reference)
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
