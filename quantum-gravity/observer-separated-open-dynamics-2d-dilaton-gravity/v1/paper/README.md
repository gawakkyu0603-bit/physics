# Manuscript Compilation Instructions (Paper 2)

This directory contains the complete LaTeX source (`main.tex`), verified BibTeX bibliography (`references.bib`), publication-grade PDF figures (`figures/`), and compiled manuscript (`main.pdf`) for:

*Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions*

## Compilation (TeX Live / `pdflatex` + `bibtex`)

```bash
cd paper
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

All figures in `figures/` can be regenerated deterministically from `../scripts/verify_paper2_sk_jt.py` (seed `20261127`).
