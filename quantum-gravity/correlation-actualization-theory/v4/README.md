# Correlation Actualization Theory

## A nonperturbative matrix proposal with observer-dependent layers

**Yohtaro Soga · Version 4 · 25 November 2026**  
English · [日本語](README.ja.md)

[Read the paper](paper/main.pdf) · [Technical supplement](paper/supplement.pdf) · [Reading guide](paper/reading-guide.md) · [Verification](VERIFICATION.md)

This version directory contains the fourth version of **Correlation Actualization Theory (CAT)**,
a proposed framework motivated by the different records available to an infalling observer
and a distant observer. Ordinary matrix dynamics creates correlations; the additional CAT
prescription allows gravity to select a layer irreversibly and change the modes available
at a later material contact.

**Status: unrefereed research preprint.** The accompanying technical reviews were generated
with AI assistance. They are part of the development and checking record; they do not
constitute journal peer review or external acceptance.

Repository: [`gawakkyu0603-bit/physics`](https://github.com/gawakkyu0603-bit/physics), with this version
under `quantum-gravity/correlation-actualization-theory/v4` and Release tag `cat-v4.0.0`.

## Read and inspect

| Purpose | Entry point |
| --- | --- |
| Main argument and physical proposal | [Article, 18 pages](paper/main.pdf) |
| Definitions, assumptions, calculations and calibration | [Technical supplement, 18 pages](paper/supplement.pdf) |
| Six physical questions and where the answers are developed | [Reading guide](paper/reading-guide.md) |
| Research results and their supporting records | [English guide to 91 numbered results](paper/evidence/result_guide.md) |
| Result-to-file and page mapping | [Evidence index](paper/evidence/experiments.json) |
| Verification history and its limits | [Publication verification summary](VERIFICATION.md), [original verification record](paper/evidence/verification.json) |
| Changes responding to the review of Version 3 | [Version 4 response](paper/response.md) |
| Original package instructions | [Unchanged original README](paper/README.md) |

The research archive includes Japanese working notes and English summaries.
The 91 numbered records describe results of different kinds, including conditional
calculations and negative results; their count is not a count of new physical laws.

## Scope of the proposal

The paper specifies a matrix prescription across matrix sizes. Its nonperturbative
calculations evaluate complete scattering blocks at **specified rank, clock, preparation
and physical port**. The [matrix-law discussion](paper/parent-history.tex) and
[observer-domain supplement](paper/supp-domains.tex) state the relevant assumptions.

- Exact closure is established for the stated constrained inward channel. A wholly
  exterior description requires closure at every accessible inward port; closing one
  angular patch does not establish that global conclusion.
- The common-source examples demonstrate specified continuations and recovery channels.
  They do not supply a general solution for a naturally collapsing star.
- A quantum theory connecting the rank and clock sectors, the widespread formation of
  the required ports in natural collapse, and recovery at the evaporation endpoint
  remain open. The proposed readout protocol is an experimental design, not a measurement.

The [formal-check appendix](paper/closing.tex) maps mathematical statements to Lean
declarations and identifies their physical and analytical inputs. Kernel checking these
conditional statements does not establish their realization in nature.

## Files and versioned downloads

Use the [`cat-v4.0.0` Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0)
for the versioned distribution. [release-assets.json](release-assets.json) records the
assets, sizes, checksums and download URLs.

| Distribution | Contents and intended use |
| --- | --- |
| Git checkout | Publication documentation in `quantum-gravity/correlation-actualization-theory/v4/`; 709 unchanged original files in its `paper/` subdirectory, including PDFs, LaTeX, research evidence, programs and Lean sources. |
| `CAT_v4_full_publication_bundle.zip` release asset | All 742 original v4 files under `CAT-review/`, including the 33 bundled runtime/dependency files omitted from Git; distribution notices and licenses are outside `CAT-review/`. Use this for the supplied offline replay wrappers. |
| GitHub-generated “Source code” ZIP or tarball | A snapshot of the Git tree. It does not include the release-only runtime payloads. |

The original files retained in `paper/` are byte-identical to the supplied fourth version.
Paths such as `paper/` in this README are relative to this version directory.
The [publication manifest](PUBLICATION_MANIFEST.json) lists every file in this directory
except the manifest itself; its paths are relative to this same directory.
The [original manifest](paper/manifest.json) describes the complete original package,
including runtime files absent from a Git checkout. Run its full integrity check against
the extracted **full publication bundle**, not the reduced Git tree.

## What has been checked

The [verification summary](VERIFICATION.md) distinguishes prior execution, source-identity
checks, and the limited checks repeated during the Version 4 technical review.

| Check | Recorded scope |
| --- | --- |
| Numerical replay | The Version 3 review reports rerunning all 9 selected drivers on Linux. Their reference comparisons cover 59 groups and 1,195 floating-point values, as well as labels, integers and array structure. |
| Lean replay | The Version 3 review reports rerunning all 10 selected modules on Linux. They contain 365 theorem or lemma declarations. The archive supplies 85 research Lean files; the selected replay is not a check of all 85. |
| Version 4 inheritance | The retained computational sources and reference outputs were compared with Version 3 by SHA-256. The detailed comparison is recorded in the verification summary. |
| Version 4 technical-review check | The package check was rerun successfully, including 143 finite inward-link systems. No full numerical-driver or Lean-module rerun is claimed for Version 4. |

The [original verification record](paper/evidence/verification.json) and
[Version 4 response](paper/response.md) preserve the earlier provenance.
The comparison policy in [numeric_policy.py](paper/numeric_policy.py) distinguishes
small nonzero quantities, physical resolution and analytical-zero residuals.

## Reproduce from the full bundle

Download `CAT_v4_full_publication_bundle.zip` from the Release, extract it to a writable
directory, and open a shell in its `CAT-review/` directory. The commands below are for
that complete package; the Git checkout does not carry the optional runtime archives.

### Linux x86-64

Use an existing CPython 3.12 interpreter on a compatible glibc system (glibc 2.28 or later).
The documented environment used CPython 3.12.3 and glibc 2.39. The wrapper installs the
bundled scientific wheels into a private cache and uses the bundled Lean binary and mathlib.

```sh
bash review-linux.sh check
bash review-linux.sh numerical cat_domain_calibration
bash review-linux.sh lean CATObserverDomain
bash review-linux.sh study RES-0183 cat_domain_calibration
```

### Windows x64

The PowerShell wrapper uses the bundled CPython 3.14.7, scientific packages and Lean 3.51.1.

```powershell
.\review-offline.ps1 -Action check
.\review-offline.ps1 -Action numerical -Names 'cat_domain_calibration'
.\review-offline.ps1 -Action lean -Names 'CATObserverDomain'
.\review-offline.ps1 -Action study -Names 'RES-0183','cat_domain_calibration'
```

Omit the names from a numerical or Lean command to run its complete default selection.
See the [original instructions](paper/README.md) for the pinned environment and command details.

## Build the manuscripts

From the `physics` repository root, with pdfLaTeX and Poppler installed:

```sh
cd quantum-gravity/correlation-actualization-theory/v4/paper
bash build.sh main supplement
```

The [article source](paper/main.tex), [supplement source](paper/supplement.tex), and
[compact article-source archive](paper/arxiv-source.tar.gz) are included.
The compact archive is an article build package; its filename does not indicate an arXiv submission.

## Human author and AI contribution

Yohtaro Soga proposed the observer-specific layers, their irreversible gravitational
selection and the distinct fates of the infaller, set exact exterior closure as the
criterion for the effective action, and directed the research. OpenAI Codex assisted
with mathematical construction, literature searches, numerical and Lean code, checks,
and drafting. Separate AI-generated technical reviews prompted corrections and clarifications.
The manuscript's [“Author contributions and use of AI” statement](paper/closing.tex)
records these roles; the human author is Yohtaro Soga.

## Citation, history and rights

Suggested identification: **Yohtaro Soga (2026), _Correlation Actualization Theory:
A nonperturbative matrix proposal with observer-dependent layers_, Version 4,
25 November 2026.** Include the `cat-v4.0.0` release or exact commit when citing this distribution.

Earlier revision responses remain available as [response-v3.md](paper/response-v3.md)
and [response-v2.md](paper/response-v2.md). No DOI, journal acceptance or institutional
affiliation is asserted by this repository description.

Consult the distribution notices and the existing licenses accompanying third-party
components for reuse conditions. This README does not add a license grant to the original work.
