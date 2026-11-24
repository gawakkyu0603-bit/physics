"""Check the shared gravitational oscillator and its distinguishable receiver modes."""
import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh_tridiagonal

ROOT = Path(__file__).resolve().parents[1]


def vacuum_energy(frequency, source, levels):
    """Diagonalize the displaced mode, taking its unperturbed vacuum as energy zero."""
    number = np.arange(levels, dtype=float)
    energies = eigh_tridiagonal(frequency * number, abs(source) * np.sqrt(number[1:]),
                                select="i", select_range=(0, 0), eigvals_only=True)
    return float(energies[0])


def two_sources():
    couplings = np.array([[.38+.07j, .16j, 0.], [.27-.11j, 0., -.12j]])
    frequencies = np.array([1.3, .90, 1.10])

    def ground(stresses, levels):
        sources = stresses @ couplings
        return sum(vacuum_energy(w, source, levels) for w, source in zip(frequencies, sources))

    base = np.array([.7, .3])
    dx, dy = np.array([.16, 0.]), np.array([0., .21])
    def difference(levels):
        return (ground(base+dx+dy, levels)-ground(base+dx, levels)
                -ground(base+dy, levels)+ground(base, levels))
    cross = -2*np.real(np.sum(np.conj(couplings[0])*couplings[1]/frequencies))
    predicted = cross*dx[0]*dy[1]
    coarse, fine = difference(18), difference(32)
    assert max(abs(fine-predicted), abs(coarse-fine)) < 1e-12
    return dict(mixed_change=predicted, diagonalization=fine, cutoff_difference=abs(fine-coarse))


def receiver(overlap, acceptance):
    """Five orthogonal modes: common, two captured, and two escaped exclusive modes."""
    common = np.sqrt(overlap)
    captured = np.sqrt(acceptance*(1-overlap))
    escaped = np.sqrt((1-acceptance)*(1-overlap))
    first = np.array([common,captured,0.,escaped,0.])
    second = np.array([common,0.,captured,0.,escaped])
    assert np.allclose([first@first,second@second,first@second],[1.,1.,overlap])
    miss1, miss2 = first[[0,3,4]], second[[0,3,4]]
    miss_probability = miss1@miss1
    mark = captured**2
    assert np.isclose(mark+miss_probability,1)
    missed_overlap = float(miss1@miss2/miss_probability) if miss_probability else None
    if missed_overlap is not None:
        assert np.isclose((1-mark)*missed_overlap,overlap)
    return dict(mark=float(mark), missed_overlap=missed_overlap)


def feedback(p_near, p_far):
    """Different physical quadrupoles after a mark, in units with hbar = 1."""
    base_stress, mark_change, first_stress = .38, .24, .65
    coordinate, step = .42, 1e-4
    def interaction(x, recorded):
        return -2*np.cos(x)*first_stress*(base_stress+mark_change*recorded)
    def mean_force(probability):
        forces = [-(interaction(coordinate+step,j)-interaction(coordinate-step,j))/(2*step)
                  for j in (0,1)]
        return (1-probability)*forces[0]+probability*forces[1]
    difference = mean_force(p_near)-mean_force(p_far)
    predicted = -2*np.sin(coordinate)*first_stress*mark_change*(p_near-p_far)
    assert abs(difference-predicted) < 1e-9
    return dict(predicted=predicted,from_potential=difference)


if __name__ == "__main__":
    near, far = receiver(.4,.85), receiver(.4,.20)
    for overlap in (0., .15, 1.):
        for acceptance in (0., .3, 1.):
            receiver(overlap,acceptance)
    results = dict(mode_energy=two_sources(),near=near,far=far,
                   causal_feedback=feedback(near["mark"],far["mark"]))
    path = ROOT/"verification"/"interacting-history-layers.json"
    path.write_text(json.dumps(results,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print(json.dumps(results,indent=2))
