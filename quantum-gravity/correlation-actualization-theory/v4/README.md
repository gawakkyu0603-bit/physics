# Correlation Actualization Theory

**A nonperturbative matrix proposal with observer-dependent layers**  
Yohtaro Soga · Version 4 · 25 November 2026

[Paper overview](../README.md) · [Main paper](paper/main.pdf) · [Technical supplement](paper/supplement.pdf) · [English introductions](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/index.html)

This directory contains the manuscript, sources, and reproduction materials for CAT Version 4. The paper studies observer-dependent records and quantum recovery in specified finite matrix constructions. Its physical assumptions and open questions are summarized in the [paper overview](../README.md#research-scope).

## Available materials

| Material | Location |
| --- | --- |
| Main paper and technical supplement | [Main PDF](paper/main.pdf) · [Supplement PDF](paper/supplement.pdf) |
| Guide to the paper's physical questions | [Reading guide](paper/reading-guide.md) |
| Research calculations and formal sources | [`paper/evidence/`](paper/evidence/) |
| LaTeX sources | [Main source](paper/main.tex) · [Supplement source](paper/supplement.tex) |
| Compact manuscript build package | [Article-source archive](paper/arxiv-source.tar.gz) |
| Complete distribution and individual downloads | [`cat-v4.0.0` Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0) |
| Distribution filenames and checksums | [Release assets](release-assets.json) · [Directory manifest](PUBLICATION_MANIFEST.json) |
| Citation | [CITATION.cff](CITATION.cff) · [BibTeX](CITATION.bib) |

The Git repository contains the manuscripts, research sources, data, and supporting files. Use `CAT_v4_full_publication_bundle.zip` from the Release for the supplied offline reproduction environment: its `CAT-review/` directory also includes runtime and dependency archives that are not stored in Git. GitHub's automatic source ZIP and tarball contain the Git tree and do not include those extra archives.

The [directory manifest](PUBLICATION_MANIFEST.json) lists the files in this version directory. The [original package manifest](paper/manifest.json) describes the complete supplied package; run its full integrity check against the extracted full bundle.

## Reproduce the calculations

Download and extract `CAT_v4_full_publication_bundle.zip` to a writable directory. Run the following commands from its `CAT-review/` directory.

### Linux x86-64

Use CPython 3.12 on a compatible glibc system, with glibc 2.28 or later. The wrapper installs the bundled scientific wheels into a private cache and uses the supplied Lean binary and mathlib.

```sh
bash review-linux.sh check
bash review-linux.sh numerical cat_domain_calibration
bash review-linux.sh lean CATObserverDomain
bash review-linux.sh study RES-0183 cat_domain_calibration
```

### Windows x64

The PowerShell wrapper uses the bundled CPython 3.14.7, scientific packages, and Lean 3.51.1.

```powershell
.\review-offline.ps1 -Action check
.\review-offline.ps1 -Action numerical -Names 'cat_domain_calibration'
.\review-offline.ps1 -Action lean -Names 'CATObserverDomain'
.\review-offline.ps1 -Action study -Names 'RES-0183','cat_domain_calibration'
```

Omit the names from a numerical or Lean command to run its complete default selection. The [Linux wrapper](paper/review-linux.sh), [Windows wrapper](paper/review-offline.ps1), and [command implementation](paper/review.py) are included in the sources. Mathematical checks establish consequences under the stated assumptions; they do not establish that those physical assumptions occur in nature.

## Build the manuscripts

From the repository root, with pdfLaTeX and Poppler installed:

```sh
cd quantum-gravity/correlation-actualization-theory/v4/paper
bash build.sh main supplement
```

The compact article-source archive is a manuscript build package. Its filename does not indicate an arXiv submission.

## Citation and rights

Cite **Yohtaro Soga (2026), _Correlation Actualization Theory: A nonperturbative matrix proposal with observer-dependent layers_, Version 4, 25 November 2026**, using the metadata linked above. Include the `cat-v4.0.0` Release or an exact commit when identifying these materials.

The manuscript contains its contribution statement. See [RIGHTS.md](RIGHTS.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) for the applicable terms. This directory does not add a license grant to the original research.
