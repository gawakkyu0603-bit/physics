# Research materials

**Observer-Separated Two-Time Quantum Dynamics: Local Horizon Obstructions, Cross-Perspective Consistency, and Finite-Dimensional Evaporation Bounds**

Yohtaro Soga · November 28, 2026

[Research overview](../README.md) · [Reading guides](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd/index.html)

| Resource | Contents |
| --- | --- |
| [Manuscript (PDF)](paper/main.pdf) | 29 pages; 56 cited references. |
| [LaTeX source](paper/main.tex) · [Bibliography](paper/references.bib) | Original source and 3 vector PDF figures. |
| [Lean sources](lean4/) · [Kernel and axiom log](lean4/VERIFICATION_LOG.txt) | 50 audited public declarations in the supplied build. |
| [Numerical code](scripts/verify_ostqd.py) · [Recorded data](docs/numerical_verification.json) | 451 scientific numeric fields, seed 20261126. |
| [Prior literature](PRIOR_ART.md) · [Verification scope](VERIFICATION.md) · [Checksums](SHA256SUMS) | Attribution, analytical boundaries and current file identities. |

## Reproduction

Run on a working copy because Python regenerates the data and figures.

```sh
python -m pip install -r scripts/requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/verify_ostqd.py
```

With elan and the supplied Lean/Mathlib configuration, run `bash verify_lean.sh` from `lean4/`. Compile from `paper/` using `pdflatex main.tex`, `bibtex main`, and two further `pdflatex main.tex` runs. See the verification scope for the exact mathematical hypotheses and analytical boundaries. Cite the manuscript and stable PDF URL (https://gawakkyu0603-bit.github.io/physics/downloads/ostqd.pdf). No new blanket license is assigned.
