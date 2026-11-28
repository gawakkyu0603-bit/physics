# Research materials

**Observer-Separated Selective Instruments, Born-Weighted Branching, and Non-Isometric Pullback Defects in Type II Gravitational Algebras**

Yohtaro Soga · November 28, 2026

[Research overview](../README.md) · [Reading guides](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd-layer2-type2/index.html)

| Resource | Contents |
| --- | --- |
| [Manuscript (PDF)](paper/main.pdf) | 31 pages; 71 cited references. |
| [LaTeX source](paper/main.tex) · [Bibliography](paper/references.bib) | Original source and 4 vector PDF figures. |
| [Lean sources](lean4/) · [Kernel and axiom log](lean4/VERIFICATION_LOG.txt) | 61 audited public declarations in the supplied build. |
| [Numerical code](scripts/verify_paper3_layer2_type2.py) · [Recorded data](docs/numerical_verification.json) | 329 scientific numeric fields, seed 20261128. |
| [Prior literature](PRIOR_ART.md) · [Verification scope](VERIFICATION.md) · [Checksums](SHA256SUMS) | Attribution, analytical boundaries and current file identities. |

## Reproduction

Run on a working copy because Python regenerates the data and figures.

```sh
python -m pip install numpy scipy matplotlib
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/verify_paper3_layer2_type2.py
```

With elan and the supplied Lean/Mathlib configuration, run `bash verify_lean.sh` from `lean4/`. Compile from `paper/` using `pdflatex main.tex`, `bibtex main`, and two further `pdflatex main.tex` runs. See the verification scope for the exact mathematical hypotheses and analytical boundaries. Cite the manuscript and stable PDF URL (https://gawakkyu0603-bit.github.io/physics/downloads/ostqd-layer2-type2.pdf). No new blanket license is assigned.
