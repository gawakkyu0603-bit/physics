# Third-party notices and data provenance

This notice accompanies **Correlation Actualization Theory, version 4**. It identifies the sources and conditions of third-party material contained in the original research package. It does not grant a new license to the CAT manuscript, its original code, or third-party data.

Paths below are relative to the original package root: `paper/` in the Git repository and `CAT-review/` in the complete release archive. The complete archive retains all 742 original files without content changes. The Git tree omits the three bundled runtime directories; obtain the complete archive to use the original offline reproduction environment. These notices are an external publication supplement and do not alter the original scientific files or their manifest.

## RIT numerical-relativity waveforms

**Source and producer:** the Center for Computational Relativity and Gravitation at Rochester Institute of Technology, [RIT Catalog](https://ccrgpages.rit.edu/~RITCatalog/).

**Source terms, checked 24 November 2026 UTC:** the official catalog labels its data **Creative Commons Attribution-NonCommercial (CC BY-NC)** and requires citations to its release papers and the simulation-specific references. The source notice does not state a Creative Commons version; no version is asserted here. A short copy of the source notice is supplied in [LICENSES/RIT-CATALOG-NOTICE.txt](LICENSES/RIT-CATALOG-NOTICE.txt). The RIT data retain their source terms, including the noncommercial condition.

The original package contains five HDF5 strain files and their five metadata files under `evidence/workspace/data/raw/rit-mergers/`, covering the following simulations. The source file hashes and provenance are retained in `evidence/workspace/data/rit-merger-files.json`. The original source metadata, including its contact and historical use labels, is preserved.

| Simulation | Resolution | Simulation-specific citation keys from the catalog |
|---|---|---|
| RIT:BBH:0001 | n100 | `Healy:2014yta`, `Healy:2016lce` |
| RIT:BBH:0045 | n100 | `Healy:2016lce` |
| RIT:BBH:0088 | n100 | `Healy:2016lce` |
| RIT:BBH:0114 | n140 | `Healy:2016lce`, `Healy:2017mvh`, `Healy:2018swt` |
| RIT:BBH:0119 | n140 | `Healy:2017mvh`, `Healy:2018swt` |

**Distribution clarification:** the original `evidence/workspace/data/RIT-MERGERS.md` says that the distribution includes only processed numbers and retrieval materials. The archived version-4 package actually includes the ten original waveform/metadata files listed above. This notice records that packaging discrepancy; the original files, their hashes, and the scientific calculations remain unchanged. The current source license notice is the CC BY-NC statement linked above; the historical `LVC-internal` label discussed in the original documentation has not been silently removed or rewritten.

The catalog release papers and the required simulation-specific papers are listed in [citations/RIT_DATA_REFERENCES.md](citations/RIT_DATA_REFERENCES.md), with machine-readable entries in [citations/rit-data-references.bib](citations/rit-data-references.bib). Include the applicable citations when reusing these data.

## Lean 3 and mathlib

The complete package includes Lean **3.51.1** and mathlib3 at commit **65a1391a0106c9204fe45bc73a039f056558cb83** under `evidence/lean-toolchain/`.

- Lean 3 source and license: [leanprover-community/lean](https://github.com/leanprover-community/lean), [official Apache-2.0 license](https://github.com/leanprover-community/lean/blob/master/LICENSE).
- mathlib3 source: [the pinned upstream revision](https://github.com/leanprover-community/mathlib3/tree/65a1391a0106c9204fe45bc73a039f056558cb83).
- A full, unmodified copy of the Apache License 2.0 is supplied in [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt). It was copied from the `LICENSE` file within the bundled mathlib source archive.

This Apache-2.0 notice applies to those third-party Lean/mathlib components. The bundled `mathlib-src.tar.gz` retains its source copyright and license notices. The binary Lean archives and mathlib cache are preserved as received. Their inclusion does not place CAT-authored material under Apache-2.0.

## CPython and Python wheels

The complete archive retains the Windows CPython **3.14.7** embedded distribution and the platform-specific wheels under `evidence/python-win64/` and `evidence/python-linux/`. The two `distributions.json` files record the pinned packages and hashes used by the original offline environment.

The embedded CPython distribution includes its original `LICENSE.txt`; an exact additional copy is supplied in [LICENSES/CPython-3.14.7.txt](LICENSES/CPython-3.14.7.txt). Each of the 26 bundled wheels includes its own license material inside the wheel. These embedded texts, including notices for dependencies bundled by the wheel maintainers, are preserved. Consult the relevant wheel's `.dist-info` license files and any additional licenses in that archive before redistribution or reuse.

## SU(2) BFSS data

The files under `evidence/workspace/data/raw/su2-bfss-layer-response/` originate from **Sergio Sanjurjo and Themistocles Zikopoulos**, [su2-bfss at the pinned revision](https://github.com/ssanjurjo/su2-bfss/tree/7fd2f16ad7b5a483ce2e3c52520819e192be3bfa). The supplied MIT copyright and permission notice is retained in that directory; an exact copy is also provided at [LICENSES/SU2-BFSS-MIT.txt](LICENSES/SU2-BFSS-MIT.txt).

| Upstream file | Name in the original CAT package |
|---|---|
| `data/profiles/solve_ch_Q4L22G16V25_r0_PR.npz` | `radial-profile.npz` |
| `data/tail_c2/final.txt` | `tail-fit.txt` |
| `LICENSE` | `LICENSE.txt` |

The original provenance record `evidence/records/literature/notes/joint-matrix-layers.md` records the source revision, correspondence, and SHA-256 hashes. This notice preserves that provenance; it does not extend the MIT grant to other datasets.

## CDT profile-header extracts

Axel Maas, Simon Plätzer, and Felix Pressler produced the data release [Stochastic samples for the CDT geon propagator from “Hints for a Geon from Causal Dynamic Triangulations,” version 1, 8 June 2026](https://zenodo.org/records/20589545), DOI [10.5281/zenodo.20589545](https://doi.org/10.5281/zenodo.20589545).

The original package's `evidence/workspace/data/CDT-DATA.md` records **CC BY 4.0** and the [license link](https://creativecommons.org/licenses/by/4.0/). That attribution and source-license statement are retained. `cdt-20589545-profiles.json` contains selected text-header extracts and provenance, not the complete original stochastic curvature-pair samples. Consult `CDT-DATA.md` for the extraction description and original archive checksums.

## Pantheon+, SPARC, and tabulated observational inputs

These inputs remain attributed to their original producers. No new blanket license is assigned to them by this repository.

| Input in `evidence/workspace/data/` | Provenance and attribution |
|---|---|
| `cat-pantheonplus-local.npz` | Derived subset of the [Pantheon+SH0ES DataRelease](https://github.com/PantheonPlusSH0ES/DataRelease), revision `c447f0fea703fcd0fff57de5000947b5ca81286b`. `cat-pantheonplus-provenance.json` records source URLs, hashes, the selection of 406 rows/344 distinct supernovae, and derived-array hashes. Cite [Brout et al., The Pantheon+ Analysis: Cosmological Constraints](https://arxiv.org/abs/2202.04077). No repository-wide license was identified on the checked upstream landing page. |
| `sparc-lelli2016c.mrt`, `sparc-rotmod-ltg.zip` | [SPARC](https://astroweb.cwru.edu/SPARC/), by Federico Lelli, Stacy McGaugh, and James Schombert. The [official publications page](https://astroweb.cwru.edu/SPARC/publications.html) identifies the master paper *SPARC: Mass Models for 175 Disk Galaxies with Spitzer Photometry and Accurate Rotation Curves*, AJ 152, 157 (2016). The source site requests citation of that master paper and consideration of the original rotation-curve references in its table. Original file URLs and hashes are retained in `evidence/records/verification/VER-0110.md`. No blanket redistribution license is added here. |
| `milky-way-eilers-table1.txt` | Eilers, Hogg, Rix, and Ness (2019), [arXiv:1810.09466](https://arxiv.org/abs/1810.09466), Table 1. The original provenance record describes a transcription of 38 rows. |
| `desi-dr2-bao-table-iv.txt` | DESI Collaboration, [DESI DR2 Results II: Measurements of Baryon Acoustic Oscillations and Cosmological Constraints, arXiv:2503.14738v2](https://arxiv.org/abs/2503.14738v2), Table IV. The source and units are retained in the file header. |

Source-level attribution and numerical provenance are provided for reproducibility. Where the source does not specify a blanket license, this notice does not infer one or promise unrestricted reuse.
