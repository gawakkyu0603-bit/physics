# OSTQD–SK/JT research materials

**Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions**

Yohtaro Soga · 27 November 2026

[Paper overview](../README.md) · [Reading guides](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd-sk-jt/index.html) · [Preceding study](../../observer-separated-two-time-quantum-dynamics/README.md)

## Materials

| Resource | Contents |
| --- | --- |
| [Manuscript (PDF)](paper/main.pdf) | 34 pages and 84 cited references. |
| [LaTeX source](paper/main.tex) · [Bibliography](paper/references.bib) · [Compilation instructions](paper/README.md) | Original source and four vector PDF figures. |
| [Lean project](lean4/README.md) · [Axiom check](lean4/OSTQD_SK/AxiomCheck.lean) · [Kernel log](lean4/VERIFICATION_LOG.txt) | 34 recorded machine-checked declarations; the formalized statements are distinguished from the continuum and physical arguments. |
| [Numerical code](scripts/verify_paper2_sk_jt.py) · [Recorded data](docs/numerical_verification.json) · [Requirements](scripts/requirements.txt) | Six numerical suites F1–F6, 258 recorded scientific numeric fields, seed 20261127. |
| [Prior literature](PRIOR_ART.md) · [Verification scope](VERIFICATION.md) | Equation-level attribution and the boundaries of the mathematical and numerical evidence. |
| [SHA-256 checksums](SHA256SUMS) · [Citation](CITATION.cff) | Original research-file identities and citation information. |

## Reproduction

Run on a working copy because the numerical program regenerates the figures and recorded data.

```sh
python -m pip install -r scripts/requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/verify_paper2_sk_jt.py
```

With elan installed and the supplied Lean/Mathlib toolchain:

```sh
cd lean4
lake exe cache get
lake build OSTQD_SK
lake env lean OSTQD_SK/AxiomCheck.lean
```

For manuscript compilation, use [the LaTeX instructions](paper/README.md). See [verification scope](VERIFICATION.md) for assumptions, original execution details and analytic steps outside the formalization. The original files are kept unchanged; publication does not claim a new blanket license. Cite the actual manuscript using [CITATION.cff](CITATION.cff).
