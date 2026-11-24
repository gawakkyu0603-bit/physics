"""Charge-constrained matrix links and preterminal radiation matching for Paper 2.

The matrices for charge acquisition and the matrices for radiative transition
amplitudes act on different factors. Frequencies x are measured in units of T_H.
The four-dimensional exterior radial solvers are supplied with this paper.
"""
import argparse
import json
from math import exp, log, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import simpson
from scipy.interpolate import PchipInterpolator

from directional_absorption import transmission
from fusion_surface_memory import greybody
from inclusive_hawking_channels import run as inclusive_channels

ROOT = Path(__file__).resolve().parents[1]


def arrows(level):
    """Normalized occupation bases, unscaled boson creation operators."""
    index = np.arange(level)
    up = np.zeros((level + 1, level))
    down = np.zeros_like(up)
    up[index, index] = np.sqrt(level - index)
    down[index + 1, index] = np.sqrt(index + 1)
    return up, down


def differential(source, target):
    blocks = []
    for a, b in zip(arrows(source), arrows(target)):
        blocks.append(np.hstack((-np.kron(np.eye(source), b),
                                 np.kron(a.T, np.eye(target + 1)))))
    return np.vstack(blocks)


def link_spectrum():
    report = []
    for n in (2, 4, 8, 12):
        for offset in (-1, 0, 1):
            m = n + offset
            d = differential(n, m)
            singular = np.linalg.svd(d, compute_uv=False)
            rank = np.count_nonzero(singular > 1e-10)
            kernel, cokernel = d.shape[1] - rank, d.shape[0] - rank
            assert kernel == max(0, offset + 1) and cokernel == max(0, -offset - 1)
            smallest = float(np.min(singular[singular > 1e-10])**2)
            if offset == -1:
                assert abs(smallest - 1/(n + sqrt(n*n - 1))) < 2e-14
            # A magnetic state can be mixed. Removing an unmeasured Schwinger
            # quantum gives an isometry only if its companion spin is retained.
            a0, a1 = arrows(n)
            hop = np.vstack((a0.T, a1.T))/sqrt(n)
            assert np.linalg.norm(hop.T@hop - np.eye(n + 1)) < 1e-14
            report.append(dict(source=n, target=m, kernel=int(kernel),
                               cokernel=int(cokernel), minimum_positive_cost=smallest))
    return report


def radial_spectra(step=.0625):
    grid = np.arange(0, 36 + step/2, step)
    x = grid[1:]
    data = {}
    for name in ("fermi", "photon"):
        if name == "fermi":
            coarse, fine = (transmission(x, 1, s) for s in (2, 4))
        else:
            coarse, fine = (greybody(x/(4*pi), 1, s, 1) for s in (2, 4))
        t = np.clip(fine + (fine - coarse)/15, 0, 1)
        u = np.exp(-x)
        if name == "fermi":
            occupation = u/(1 + u)
            singly_filled = u/(1 + u)**2
        else:
            occupation = u/(1 - u)
            singly_filled = u*(1 - u)**2
        integrate = lambda f: float(simpson(np.r_[0., f], x=grid))
        number = integrate(t*occupation)
        energy = integrate(x*t*occupation)
        single = integrate(t*singly_filled)
        interpolant = PchipInterpolator(grid, np.r_[0., t])
        data[name] = (interpolant, dict(I0=number, I1=energy, single=single,
                          eligible_per_entropy=single/energy,
                          missing_at_1000_nats_and_tenth_power=exp(-100*single/energy)))
    return data


def amplitudes(n, m, interpolant, name):
    """Regularized on-shell vertices. m>=n cannot emit into empty exterior modes."""
    valid = m < n
    x = np.zeros(m.shape)
    np.log(n/m, where=valid, out=x)
    trans = interpolant(np.minimum(x, 36.))
    denominator = n+m if name == "fermi" else n-m
    weight = np.divide(trans, denominator, where=valid, out=np.zeros(m.shape))
    return x, np.sqrt(weight)


def spectrum_test(data):
    table = {}
    for name, (interpolant, baseline) in data.items():
        rows = []
        for number in (64, 256, 1024, 4096, 16384, 65536, 262144, 1048576):
            m = np.arange(1, number, dtype=float)
            x, amp = amplitudes(number, m, interpolant, name)
            weight = amp**2
            rows.append(dict(number=number, number_integral=float(np.sum(weight)),
                             energy_integral=float(weight@x),
                             relative_energy_error=float((weight@x)/baseline["I1"]-1)))
        assert abs(rows[-1]["relative_energy_error"]) < .0004
        table[name] = dict(continuum=baseline, rows=rows)
    return table


def interference_test(data):
    # Parent levels in an aligned binary block. Distinct daughter masses are
    # orthogonal. The two preparations with fixed daughter have nearly the
    # same radiation energy across the much narrower incoming code band.
    interp = data["fermi"][0]
    report = []
    for n, dimension in [(256, 8), (2048, 8), (8192, 16), (32768, 16), (32768, 32)]:
        m = np.arange(1, n+dimension, dtype=np.int64)
        residue = np.arange(dimension)
        walsh = np.array([[1-2*((j & int(r)).bit_count()%2) for r in residue]
                           for j in range(dimension)])
        assert np.array_equal(walsh@walsh.T, dimension*np.eye(dimension, dtype=int))
        rows = np.array([amplitudes(n+j, m, interp, "fermi")[1] for j in range(dimension)])
        mean = np.sum(rows**2)/dimension
        equal_sign = rows@rows.T/mean
        signed = rows*walsh[:, m%dimension]
        honest = signed@signed.T/mean
        # Check the underlying exact residue formula with weights frozen at n.
        base_weight = rows[0]**2
        by_residue = np.array([sum(base_weight[m%dimension == k]) for k in residue])
        fixed = walsh[:, m%dimension]*rows[0]
        np.testing.assert_allclose(np.linalg.eigvalsh(fixed@fixed.T),
                                   np.sort(dimension*by_residue), rtol=3e-13)
        # A recorded daughter residue would expose a logical Walsh basis.
        probs = (walsh@signed/sqrt(dimension))**2
        proper = np.array([sum(probs[k, m%dimension == k])/sum(probs[k])
                           for k in residue])
        plus_minus = np.array([1., -1.] + [0.]*(dimension-2))/sqrt(2)
        eig = np.linalg.eigvalsh(honest)
        report.append(dict(n=n, dimension=dimension, common_phase_dark_rate=float(
                               plus_minus@equal_sign@plus_minus),
                           common_phase_maximum=float(np.linalg.eigvalsh(equal_sign)[-1]),
                           walsh_minimum=float(eig[0]), walsh_maximum=float(eig[-1]),
                           worst_correct_residue=float(min(proper))))
    assert report[-1]["walsh_minimum"] > .95 and report[-1]["common_phase_dark_rate"] < 1e-6
    return report


def handoff_test(data):
    interp = data["fermi"][0]
    sizes = [512, 4096, 32768]
    stop = 8
    report = []
    for n in sizes:
        m = np.arange(1, stop+1)
        x, amp = amplitudes(n, m, interp, "fermi")
        eta = stop/n
        count, energy = float(amp@amp), float((amp**2)@x)
        assert count <= eta and energy <= eta*(1-log(eta))
        report.append(dict(n=n, stop=stop, number_mass=count, number_bound=eta,
                           energy_mass=energy, energy_bound=eta*(1-log(eta))))
    return report


def figure(path, report):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, panels = plt.subplots(2, 2, figsize=(8.3, 5.7), layout="constrained")
    axes = panels.ravel()
    for name, label in [("fermi", "Massless fermion"), ("photon", "Photon")]:
        table = report["spectrum"][name]["rows"]
        axes[0].loglog([r["number"] for r in table],
                       [abs(r["relative_energy_error"]) for r in table], "o-", label=label)
    axes[0].set(xlabel="Parent level", ylabel="Relative error in energy flux")
    axes[0].legend(frameon=False, fontsize=8)
    rows = [r for r in report["interference"] if r["dimension"] in (8, 16)]
    n = np.array([r["n"] for r in rows])
    axes[1].loglog(n, [r["common_phase_dark_rate"] for r in rows], "o-", label="Equal signs, dark input")
    axes[1].loglog(n, [r["walsh_minimum"] for r in rows], "s-", label="Binary signs, weakest input")
    axes[1].set(xlabel="Parent level", ylabel="Rate / mean diagonal rate")
    axes[1].legend(frameon=False, fontsize=8)
    species = report["inclusive"]["massless"]
    channels = ("neutrino", "photon", "graviton")
    position = np.arange(len(channels))
    axes[2].bar(position-.18, [species[c]["power_fraction"] for c in channels], .36,
                label="Fraction of total power")
    axes[2].bar(position+.18, [species[c]["maximum_entropy_per_total_area_nat"] for c in channels],
                .36, label="Max. entropy / lost area nat")
    axes[2].set(xticks=position, xticklabels=("Neutrinos", "Photons", "Gravitons"),
                ylabel="Fraction or nats per nat")
    axes[2].legend(frameon=False, fontsize=8)
    scalar = report["inclusive"]["massive"]["scalar"]
    axes[3].semilogy([r["mass_over_T"] for r in scalar],
                     [r["fraction_of_massless_s_wave"] for r in scalar], "o-")
    axes[3].set(xlabel="Rest mass / Hawking temperature",
                ylabel="Scalar power / massless s-wave power")
    fig.savefig(path)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", type=Path)
    args = parser.parse_args()
    data = radial_spectra()
    result = dict(links=link_spectrum(), spectrum=spectrum_test(data),
                  interference=interference_test(data), handoff=handoff_test(data),
                  inclusive=inclusive_channels(amplitudes))
    (ROOT/"verification/preterminal-matching-results.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False)+"\n", encoding="utf8")
    if args.figure:
        figure(args.figure, result)
    print("Charge links, four-dimensional preterminal radiation and unresolved phases checked.")
