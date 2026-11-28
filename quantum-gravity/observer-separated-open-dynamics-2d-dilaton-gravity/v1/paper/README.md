# Manuscript Compilation Instructions

This directory contains the complete LaTeX source (`main.tex`), verified BibTeX bibliography (`references.bib`), pre-built BibTeX output (`main.bbl`), publication-grade vector PDF figures (`figures/`), and compiled manuscript (`main.pdf`, 42 pages, 94 cited references) for:

*Consistency Audits of Observer-Separated Open Dynamics in 2D Dilaton Gravity: KMS Covariance, Non-Gaussian JT Fluctuations, and Chiral-Horizon Obstructions*

## Compilation (TeX Live / `pdflatex` + `bibtex`)

```bash
cd paper
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex
```

All four figures in `figures/` can be regenerated deterministically from `../scripts/verify_paper2_sk_jt.py` (seed `20261127`, dependencies pinned in `../scripts/requirements.txt`).
