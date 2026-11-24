"""Same final gravitational instrument on correlated and exchangeable receipts."""
from pathlib import Path
import json

import numpy as np
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parents[1]


def probabilities(common, difference, dimension, exchange):
    indices = np.arange(dimension)
    # Common spectrum m/L; transfer basis is its conjugate Fourier basis.
    phase = np.exp(-1j * common * indices / dimension)
    common_prob = abs(np.fft.ifft(phase))**2
    q, vectors = np.linalg.eigh(exchange)
    central = len(q)//2
    transfer = abs(vectors @ (np.exp(-1j * difference*q) * vectors[central].conj()))**2
    return np.outer(common_prob, transfer)


def rotor_local_read():
    """Common and differential modes share the compact M2 spectrum.

    The clocks are ordinary receiver records independent of the four local
    alternatives. The integrations use analytic window transforms, with no
    choice of a clock value after seeing an outcome.
    """
    from math import comb, pi
    from scipy.constants import c, h, hbar

    spin = 191
    wave_length = 28.22e-6
    charge_step = h*c/wave_length
    width = 1e-6
    gap_floor = 6.29e-6
    weights = np.array([comb(2*k, k)*comb(2*(spin-k),spin-k)/4**spin for k in range(spin+1)])
    contrast = np.linspace(-1.,1.,spin+1)
    impact, height = 4., .05
    theta = np.arccos(contrast)
    patch = 1+height*sum((1+((theta+2*pi*n)/impact)**2)**-3 for n in range(-140,141))
    lapse = patch**(-1/3)
    collision = float(weights@weights)
    dphase = charge_step*width*(lapse[:,None]-lapse[None,:])/hbar
    minphase = charge_step*width*gap_floor/hbar
    uniform_ceiling = collision+(1-collision)*min(1.,2/minphase)
    expon_ceiling = collision+(1-collision)/(1+minphase**2)
    pair_weights = np.outer(weights,weights)
    uniform = []
    exponential = []
    for separation in (1,2,3):
        u = separation*dphase
        # A clock uniformly distributed in [1,2] microseconds.
        uniform.append(float(np.sum(pair_weights*np.sinc(u/(2*pi))*np.cos(1.5*u))))
        exponential.append(float(np.sum(pair_weights/(1+u*u))))
    assert max(uniform)<=uniform_ceiling and max(exponential)<=expon_ceiling
    # Direct square-root measurement with three untuned, distinct receiver times.
    # An energy-degenerate reference copy supplies the conjugate comparison.
    gram=np.ones((4,4),dtype=complex)
    for ratio in (1.11,1.39,1.82):
        x = np.arange(4)[:,None]-np.arange(4)[None,:]
        gram*=np.sum(weights*np.exp(1j*x[:,:,None]*ratio*charge_step*width*(lapse-lapse[0])/hbar),axis=2)
    ev,vec=np.linalg.eigh(gram)
    square_root=(vec*np.sqrt(np.maximum(ev,0)))@vec.conj().T
    errors=1-abs(np.diag(square_root))**2
    row_bounds=np.sum(abs(gram-np.eye(4))**2,axis=0)
    assert max(errors-row_bounds)<1e-12
    return dict(wavelength_um=wave_length*1e6, charge_eV=charge_step/1.602176634e-19,
                minimum_gap=gap_floor, duration_window_s=width, dimensionless_min_phase=minphase,
                uniform_mean_ceiling=uniform_ceiling, exponential_mean_ceiling=expon_ceiling,
                uniform_pair_means=uniform, exponential_pair_means=exponential,
                two_read_average_error_ceiling=3*uniform_ceiling**2,
                three_read_average_error_ceiling=3*uniform_ceiling**3,
                exponential_two_read_error_ceiling=3*expon_ceiling**2,
                three_fixed_read_errors=errors.tolist(), three_fixed_read_bounds=row_bounds.tolist())


def main():
    levels, size = 4, 7
    prior = np.array([.10,.20,.31,.39])
    # Ordinary isometry |h,0> -> |h,h> preserves the entire input before selection.
    prepare = np.eye(levels**2).reshape(levels**2, levels, levels)
    correlate = np.column_stack([prepare[:,h,h] for h in range(levels)])
    psi = np.sqrt(prior)*np.exp(1j*np.array([0., .7, -.3, .2]))
    assert abs(np.vdot(psi, correlate.conj().T @ correlate @ psi)-1)<1e-14
    # A splitting instrument with two continuous outcomes distinguished only by
    # their densities; integrating the layer coordinate returns the original Born marginal.
    a = np.array([.12,-.43,.65,-.21])
    angles = 2*np.pi*(.5+np.arange(512))/512
    born_density = prior[:,None]*(1+a[:,None]*np.cos(angles))
    assert np.max(abs(born_density.mean(axis=1)-prior))<1e-15

    # A chiral transfer unitary makes the sign physically detectable whenever
    # a label telling which incoming current was first is also retained.
    rng = np.random.default_rng(11922)
    raw = rng.normal(size=(size,size)) + 1j*rng.normal(size=(size,size))
    exchange = (raw+raw.conj().T)/(3*size)
    central = size//2
    local = np.array([probabilities(2*np.pi*h,0.,levels,exchange) for h in range(levels)])
    far = np.zeros_like(local)
    tagged = np.zeros((levels, 2, levels, size))
    # Both received stresses are nonnegative. Common sum and absolute difference
    # may be correlated; only their sign permutations must have invariant weights.
    pairs = [(1., 2.3, .19), (.7, 4.1, .35), (3.2, 6.4, .46)]
    for h in range(levels):
        sign = 1 if h%2==0 else -1
        for lo,hi,weight in pairs:
            for orientation in (0,1):
                diff = sign*(1-2*orientation)*(hi-lo)
                law = probabilities((hi+lo)/2,diff,levels,exchange)
                far[h] += weight*law/2
                tagged[h,orientation] += weight*law/2
    assert np.max(abs(far-far[0])) < 3e-15
    assert min(local[h,h,central] for h in range(levels))>1-1e-14
    local_success = float((prior[:,None,None]*local).max(axis=0).sum())
    far_success = float((prior[:,None,None]*far).max(axis=0).sum())
    tag_success = float((prior[:,None,None,None]*tagged).max(axis=0).sum())
    assert abs(far_success-max(prior))<1e-14 and tag_success>far_success
    no_selection = np.outer(psi,psi.conj())
    after_selection = np.diag(prior)
    echo = np.vdot(psi,after_selection @ psi).real
    assert abs(echo-np.dot(prior,prior))<1e-14
    # Same physical spectrum--independent tests using a referenced common state and
    # a mismatched radial port, including a complex Hermitian exchange matrix.
    neutral = np.eye(size)[:,central]
    error_pairs = []
    for c1,c2 in ((.2,1.7),(-.9,3.2),(2.,2.)):
        u = expm(-1j*c1*exchange)@neutral
        v = expm(-1j*c2*exchange)@neutral
        prior_difference=(np.outer(u,u.conj())-np.outer(v,v.conj()))/2
        optimal=(1-np.abs(np.linalg.eigvalsh(prior_difference)).sum())/2
        radial=abs(np.vdot(neutral,expm(-1j*(c2-c1)*exchange)@neutral))**2
        assert abs(4*optimal*(1-optimal)-radial)<3e-15
        error_pairs.append([c2-c1,float(optimal),float(radial)])
    # Exact bright-state gravitational splitting, including the null event.
    splitting = []
    ell = 2*np.pi*(np.arange(1024)+.5)/1024
    for g in ((0j,0j),(.3+.2j,-.5+.07j),(1.-.13j,.16+.81j)):
        g=np.array(g)
        vertex=np.zeros((3,3),dtype=complex)
        vertex[1:,0]=g; vertex[0,1:]=g.conj()
        state=expm(-1j*.75*vertex)[:,0]
        mark=float(np.mean(abs(state[1]+np.exp(-1j*ell)*state[2])**2))
        expected=np.sin(.75*np.linalg.norm(g))**2
        assert abs(mark-expected)<1e-15 and abs(abs(state[0])**2+mark-1)<1e-15
        splitting.append([float(np.linalg.norm(g)),float(expected),mark])
    delta = .2
    correct = probabilities(2*np.pi+delta,0.,levels,exchange)[1,central]
    lower = float(np.sinc(delta/(2*np.pi))**2)
    assert correct>=lower
    # Small but positive auxiliary measurement of the fine history; its later
    # deletion must not be mistaken for an observer who never selected it.
    eig = np.linalg.eigvalsh(no_selection-after_selection)
    result = dict(rotor_local_read=rotor_local_read(), prior=prior.tolist(), matched_binary=error_pairs, bright_vertex=splitting, minimum_local_read=float(min(local[h,h,central] for h in range(levels))),
                  local_guess=local_success, remote_guess=far_success,
                  remote_with_side_information=tag_success, maximum_remote_row_error=float(np.max(abs(far-far[0]))),
                  example_remote_radial=float(far[0,:,central].sum()),
                  split_normalization_error=float(max(abs(born_density.mean(axis=1)-prior))),
                  local_radial=float(local[0,:,central].sum()), initial_coherent_echo=1.,
                  post_selection_coherent_echo=float(echo),
                  trace_distance_after_forgetting=float(np.abs(eig).sum()/2),
                  detuning=delta, correct_at_detuning=float(correct), analytic_lower=lower)
    (ROOT/'verification'/'observer-conditioned-receipts-results.json').write_text(
        json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print("Best local, remote, remote with extra mark:",local_success,far_success,tag_success)
    print("Local radial fraction and echo:",result['local_radial'],echo)


if __name__ == "__main__":
    main()
