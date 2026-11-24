"""Reduce RIT strain multipoles to two time-resolved four-momentum transfers.

Python with h5py, NumPy and SciPy; --fetch retrieves the original public files.
The reduction contains integrated quantities only. Units are G=c=M_initial=1.
"""
import argparse
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen

import numpy as np
from scipy.integrate import cumulative_trapezoid
from scipy.interpolate import InterpolatedUnivariateSpline
from scipy.linalg import expm

ROOT = Path(__file__).resolve().parents[1]
RAW = ROOT / "data/raw/rit-mergers"
BASE = "https://ccrgpages.rit.edu/~RITCatalog/"
MANIFEST = ROOT / "data/rit-merger-files.json"
OUTPUT = ROOT / "data/processed/rit-merger-flux.json"
MODES = [(ell, m) for ell in range(2, 5) for m in range(-ell, ell + 1)]
SPEED_KMS = 299792.458


def source_files(case, fetch):
    paths = []
    for item in case["sources"]:
        path = RAW / item["path"].split("/")[-1].replace(":", "-")
        if not path.is_file() and fetch:
            with urlopen(BASE + item["path"], timeout=70) as stream:
                content = stream.read()
            if hashlib.sha256(content).hexdigest() != item["sha256"]:
                raise ValueError(f"Source differs from registered version: {path.name}")
            RAW.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        if not path.is_file():
            raise FileNotFoundError(f"{path.name} is absent; rerun with --fetch")
        if hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError(f"Checksum mismatch: {path.name}")
        paths.append(path)
    return paths


def direction_matrices():
    # Integer-spin rotation, Condon--Shortley convention, spin weight s=-2.
    nodes, weights = np.polynomial.legendre.leggauss(24)
    radial = np.zeros((len(nodes), len(MODES)))
    for ell in range(2, 5):
        m = np.arange(-ell, ell)
        raising = np.diag(np.sqrt(ell * (ell + 1) - m * (m + 1)), -1)
        jy = (raising - raising.T) / (2j)
        columns = [i for i, (order, _) in enumerate(MODES) if order == ell]
        for row, x in enumerate(nodes):
            rotation = expm(-1j * np.arccos(x) * jy)
            radial[row, columns] = np.sqrt((2 * ell + 1) / (4 * np.pi)) * rotation[:, ell + 2].real
    m = np.array([mode[1] for mode in MODES])
    difference = m[:, None] - m[None, :]
    def matrix(weight, change):
        return (2 * np.pi * radial.T @ ((weights * weight)[:, None] * radial)) * (difference == change)
    assert np.allclose(matrix(1, 0), np.eye(len(MODES)), rtol=0, atol=4e-14)
    return matrix(np.sqrt(1 - nodes**2), 1), matrix(nodes, 0)


def strain_news(file, time):
    strain, news = [], []
    for ell, m in MODES:
        def spline(field):
            group = file[f"{field}_l{ell}_m{m}"]
            return InterpolatedUnivariateSpline(group["X"][:], group["Y"][:], k=int(group["deg"][()]))
        amplitude, phase = spline("amp"), spline("phase")
        a, phi = amplitude(time), phase(time)
        carrier = np.exp(1j * phi)
        strain.append(a * carrier)
        news.append((amplitude.derivative()(time) + 1j * a * phase.derivative()(time)) * carrier)
    return np.array(strain).T, np.array(news).T


def four_flux(news, transverse, vertical):
    scale = 1 / (16 * np.pi)
    # N_i* <i|n|j> N_j. Only adjacent m contribute to the transverse impulse.
    def contract(mat):
        return np.sum(news.conj() * (news @ mat.T), axis=1)
    xy = contract(transverse)
    return scale * np.column_stack((np.sum(abs(news)**2, axis=1), xy.real, xy.imag, contract(vertical).real))


def reduce_case(case, matrices, fetch):
    import h5py
    path, metadata = source_files(case, fetch)
    fields = dict(line.split("=", 1) for line in metadata.read_text().splitlines()
                  if "=" in line and not line.startswith("#"))
    fields = {k.strip(): v.strip() for k, v in fields.items()}
    with h5py.File(path) as f:
        # Stay inside every ROM spline's domain and use the same cuts at all refinements.
        xmin = max(f[k]["X"][0] for k in f if k.startswith(("amp_", "phase_")))
        xmax = min(f[k]["X"][-1] for k in f if k.startswith(("amp_", "phase_")))
        t = np.arange(np.ceil(xmin * 8) / 8, min(xmax, 140.), .125)
        if xmin > -450 or xmax < 100:
            raise ValueError(f"insufficient shared interval in {path.name}: {xmin}, {xmax}")
        strain, news = strain_news(f, t)
    flux = four_flux(news, *matrices)
    peak_index = np.argmax(flux[(t > -20) & (t < 20), 0]) + np.flatnonzero(t > -20)[0]
    peak = t[peak_index]
    index = lambda value: int(np.searchsorted(t, value))
    # Gently turn on the earliest waves to reduce the unknown integration constant.
    # The alternate unwindowed and shifted tapers are included in the output.
    def integral(f, start, rise, step=1):
        u = np.clip((t - start) / rise, 0, 1) if rise else None
        weight = .5 * (1 - np.cos(np.pi*u)) if rise else (t >= start).astype(float)
        return cumulative_trapezoid((f*weight[:, None])[::step], t[::step], axis=0, initial=0)
    def segments(cumul, cut, step=1):
        center, end = index(peak+cut), index(peak+80)
        # Interpolate cumulative transfers to common physical boundaries.
        def value(row):
            return np.array([np.interp(t[row], t[::step], v) for v in cumul.T])
        early, total = value(center), value(end)
        return {"early":early.tolist(), "late":(total-early).tolist()}
    initial = t[0]
    base = integral(flux, initial, 100)
    cuts = {str(c):segments(base,c) for c in (-20,-10,0,10,20)}
    sensitivity = {"half_rate":segments(integral(flux,initial,100,2),0,2),
                   "late_taper":segments(integral(flux,-450,100),0),
                   "sharp_start":segments(integral(flux,initial,0),0)}
    low_modes = news.copy()
    low_modes[:, [ell == 4 for ell, _ in MODES]] = 0
    sensitivity["ell_le_3"] = segments(integral(four_flux(low_modes,*matrices),initial,100),0)
    finite_derivative = np.gradient(strain, t, axis=0, edge_order=2)
    sensitivity["centered_derivative"] = segments(integral(four_flux(finite_derivative,*matrices),initial,100),0)
    if np.max(np.linalg.norm(flux[:,1:],axis=1)-flux[:,0]) > 1e-13:
        raise ArithmeticError("Noncausal flux")
    return {"q":float(fields["initial-mass1"])/float(fields["initial-mass2"]),
            "remnant_mass":float(fields["final-mass"]), "remnant_spin":float(fields["final-chi"]),
            "initial_adm_energy":float(fields["initial-ADM-energy"]),
            "metadata_kick_kms":float(fields["final-kick"]), "peak_time_M":float(peak),
            "start_time_M":float(initial), "cut_offsets_M":cuts, "sensitivity":sensitivity}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true")
    args = parser.parse_args()
    sources = json.loads(MANIFEST.read_bytes())
    matrices = direction_matrices()
    rows = {case["id"]:reduce_case(case, matrices, args.fetch) for case in sources["cases"]}
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(rows, indent=2, allow_nan=False)+"\n",encoding="utf8")
    for case, row in rows.items():
        pair = row["cut_offsets_M"]["0"]
        early, late = np.array(pair["early"])[1:], np.array(pair["late"])[1:]
        unit = SPEED_KMS / row["remnant_mass"]
        print(case, np.round([unit*np.linalg.norm(early+late),unit*np.hypot(np.linalg.norm(early[:2]),np.linalg.norm(late[:2]))],3))


if __name__ == "__main__":
    main()
