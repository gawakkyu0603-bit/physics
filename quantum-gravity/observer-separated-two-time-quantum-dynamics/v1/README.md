# OSTQD research materials

**Observer-Separated Two-Time Quantum Dynamics: Local Horizon Obstructions, Cross-Perspective Consistency, and Finite-Dimensional Evaporation Bounds**

Yohtaro Soga · 26 November 2026

[Research overview](../README.md) · [English reading guides](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/ostqd/index.html)

## Materials

| Resource | Description |
| --- | --- |
| [Manuscript (PDF)](paper/main.pdf) | 24-page paper, including the mathematical results and finite-model calculations. |
| [LaTeX source](paper/main.tex) · [Bibliography](paper/references.bib) | Source and references for the manuscript. |
| [Lean sources](lean4/OSTQD/) · [Recorded kernel build and axiom checks](lean4/VERIFICATION_LOG.txt) | Finite-dimensional algebraic core, 38 public declarations. |
| [Numerical code](scripts/verify_ostqd.py) · [Recorded results](docs/numerical_verification.json) | Matrix identities, channel examples, evaporation model, and Galerkin benchmark. |
| [Horizon heating](paper/figures/fig1_horizon_heating.pdf) · [Joint recovery and bottleneck](paper/figures/fig2_joint_vs_separated.pdf) · [Evaporation model](paper/figures/fig3_matrix_evaporation.pdf) | Original figures. |
| [SHA-256 checksums](SHA256SUMS) | Original research-file identities. |

## Reproduce the calculations

The numerical code requires Python 3.10 or later, NumPy, SciPy and Matplotlib. Run on a working copy, because the script regenerates the recorded JSON and figures:

```sh
python -m pip install numpy scipy matplotlib
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python scripts/verify_ostqd.py
```

The Lean toolchain and Mathlib dependency are pinned by the supplied configuration. With elan installed:

```sh
cd lean4
lake exe cache get
lake build OSTQD
lake env lean OSTQD/AxiomCheck.lean
```

The original log records the kernel build and standard axioms. Section 8 of the manuscript distinguishes the algebraic statements checked in Lean from analytic and physical steps outside that formalization.

To compile the manuscript with TeX Live:

```sh
cd paper
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

## Citation and use

Cite Yohtaro Soga, *Observer-Separated Two-Time Quantum Dynamics: Local Horizon Obstructions, Cross-Perspective Consistency, and Finite-Dimensional Evaporation Bounds*, 26 November 2026. The paper contains the author contribution statement and the research's assumptions and limitations. No new blanket license is assigned to the original materials.
