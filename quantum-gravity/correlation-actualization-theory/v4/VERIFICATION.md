# Version 4 verification and provenance

This summary distinguishes actual execution, identity checks and the limits of
the scientific claims. The technical reviews were AI-assisted development reviews,
not journal peer review or independent human-expert acceptance.

## Original Version 4 identity

| Item | Value |
| --- | --- |
| Manuscript date | 25 November 2026 |
| Original received archive | `CAT_再査読用一式_第4版.zip` |
| Original archive size | 303,175,654 bytes |
| Original archive SHA-256 | `fad61f93e3915de81701d9ebe8f3326c8a66fbb23c1a16572ee8aac7609fa14f` |
| Original expanded payload | 742 files; 311,006,260 bytes |
| Original manifest | 741 entries, excluding the manifest itself |
| Article | 18 pages; SHA-256 `5b3539369c18b900a207c1bf8e55e3261a7e9599b6cd8be8181f7c814c68fc7a` |
| Supplement | 18 pages; SHA-256 `96c59915ad3bdafbad4da6b79bb9974f3ba7a644544205070691383fa16b46a8` |

The full publication ZIP is a **new distribution wrapper**. It preserves every
original file under `CAT-review/` and adds distribution notices outside that
directory. Its ZIP checksum therefore differs from the original received ZIP.
`SHA256SUMS` in the release records the checksums of the downloadable assets.

The Git tree retains 709 original files under this version directory's `paper/`
(23,463,032 bytes), at `quantum-gravity/correlation-actualization-theory/v4/paper/`
in `gawakkyu0603-bit/physics`. The Release tag is `cat-v4.0.0`.
It omits only the three bundled environment directories
`evidence/lean-toolchain`, `evidence/python-linux`, and `evidence/python-win64`:
33 files, 287,543,228 bytes. Those files remain in the full publication ZIP.
GitHub's automatically generated source archive is a copy of the Git tree, not
the full offline publication bundle.

## Execution and identity checks

| Stage | What was checked | What this supports |
| --- | --- | --- |
| Version 3 technical review | All 9 selected numerical drivers and all 10 selected Lean modules were rerun on Linux, as recorded in the review and the v4 response. Numerical comparisons cover 59 groups and 1,195 floating-point values. The selected modules contain 365 theorem/lemma declarations. | Reproduction of the selected finite calculations and conditional formal statements in the stated environment. |
| Version 4 technical review | All 33 selected execution sources, reference outputs and wrappers are byte-identical to v3. All 309 workspace files and the 91 numbered result records are unchanged. Eighteen checked Linux/Lean dependency files also match. | The v3 execution evidence applies to the unchanged v4 inputs; this is source-identity evidence, not a new full rerun. |
| Version 4 package check | The supplied `check` entry point exited successfully and reported 143 independent finite-link counts passed. | Integrity and the specified finite-link calculations. |
| Version 4 editorial review | The changed manuscript, supplement, response, reading guide and calculation-sheet explanations were examined. The article-source archive's 8 files match the corresponding current sources. | Consistency of the editorial revision and its stated scope. |
| Publication packaging | All 742 original files were compared with the received ZIP; all original manifest entries matched and ZIP CRC testing passed. The 709 files retained in Git are copied without changing their bytes. | Identity of the distributed original material. This is not a scientific or legal certification. |

The v4 archive comparison found **717 unchanged files, 23 changed files and
2 added files**, with no removed files. Changes are documented in the
[v4 response](paper/response.md). The comparison of computational inputs above
is narrower than claiming that every file in v4 is identical to v3.

The full nine-driver and ten-module suites were **not rerun during the Version 4
review**. The previous successful executions were inherited by identity checks.
The archive supplies 85 research Lean files, but the selected replay covers 10
modules; a count of supplied files is not a count of independently checked modules.

## Evidence and reproduction

- [Original verification record](paper/evidence/verification.json)
- [Version 4 response and review provenance](paper/response.md)
- [Original manifest](paper/manifest.json)
- [Research result guide](paper/evidence/result_guide.md)
- [Numerical comparison policy](paper/numeric_policy.py)
- [Formal assertions and their assumptions](paper/closing.tex)
- [Machine-readable publication verification summary](verification-summary.json)

For the complete supplied Linux and Windows reproduction entry points, download
the full publication ZIP and follow this version's
[README](README.md). Run the original
manifest check in its complete `CAT-review/` directory. It will report missing
runtime files if run unchanged against the reduced Git checkout.

## Interpretation

The reported checks support the declared finite, conditional construction.
Lean checking does not verify the physical realization of the supplied ports,
clocks, instruments or data. The readout calibration is a proposed experiment,
not an observed gravitational signal. An all-rank/continuum theory, a physical
measure across sectors, generic natural collapse and endpoint recovery remain
open as stated in the manuscript.
