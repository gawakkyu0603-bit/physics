# Correlation Actualization Theory — Version 4 publication scope

This record describes the distribution, provenance, companion guides, and scientific limits of CAT Version 4. Repository-wide policy is maintained separately in [Publication scope](../../../docs/PUBLICATION_SCOPE.md).

[CAT and its versions](../README.md) · [Version 4 materials and reproduction](README.md) · [Guide coverage](reading-guides/COVERAGE.md) · [Scientific QA](reading-guides/SCIENTIFIC_QA.md)

## Identity and distribution

| Item | Value |
| --- | --- |
| Manuscript | *Correlation Actualization Theory: A nonperturbative matrix proposal with observer-dependent layers* |
| Author | Yohtaro Soga |
| Manuscript version and date | Version 4 · 25 November 2026 |
| Repository | [`gawakkyu0603-bit/physics`](https://github.com/gawakkyu0603-bit/physics) |
| Version directory | `quantum-gravity/correlation-actualization-theory/v4/` |
| Namespaced release tag | `cat-v4.0.0` |
| Release | <https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0> |
| Original source at the release tag | [Version 4 original files](https://github.com/gawakkyu0603-bit/physics/tree/cat-v4.0.0/quantum-gravity/correlation-actualization-theory/v4/paper) |

The repository hierarchy is physics → field → paper → version. Version 4 identifies this CAT manuscript and distribution; it is not a version number for all physics research in the repository.

## English companion guides for Version 4

The [CAT reading-page entry](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/index.html) links the three English audience guides.

| Audience | English page path | Figures in the Version 4 guide |
| --- | --- | ---: |
| Research specialists | [`docs/en/quantum-gravity/cat/expert.html`](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/expert.html) | 8 |
| STEM students and graduates | [`docs/en/quantum-gravity/cat/student.html`](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/student.html) | 9 |
| General readers | [`docs/en/quantum-gravity/cat/general.html`](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/general.html) | 9 |

Public URLs use `https://gawakkyu0603-bit.github.io/physics/` followed by the page path with the leading `docs/` removed. Every guide begins with a TL;DR and covers the paper and supplement at its intended reader's level. The amount of explanation, vocabulary, equations, and figures is adapted to the audience while preserving assumptions, data meanings, conclusions, and limitations.

Coverage extends from motivation and interaction choices through states, channels, physical domains, material currents, matrix dynamics, histories, deadlines, quantum recovery, the common-source fixture, clocks and finite sectors, geometry, shared spacetime, other theories, vacua and radius stability, laboratory and astronomical tests, cosmology, verification, and open questions. Reader-specific reference material links the testing proposals to the technical supplement. The [coverage table](reading-guides/COVERAGE.md) and [scientific QA record](reading-guides/SCIENTIFIC_QA.md) retain the detailed mappings, checks, corrections, and unverified scope.

These are companion explanations of the fourth version. They do not alter the original paper, create new physical evidence, or transform a conditional construction into an observed result. The live site follows the version selected in the [current catalog](../../../site-src/catalog.json); these unversioned reading-page URLs may later present a newer version. Use the immutable `cat-v4.0.0` tag and Release for Version 4 research materials, and retain this version's companion-guide records when the catalog advances.

## Original material and complete download

The [verification statement](VERIFICATION.md) is the detailed provenance record.

| Distribution | Scope |
| --- | --- |
| Version directory's `paper/` | 709 original files, 23,463,032 bytes, retained without changes |
| Release-only runtime payload | 33 original files, 287,543,228 bytes, from `evidence/lean-toolchain`, `evidence/python-linux`, and `evidence/python-win64` |
| Full publication ZIP | All 742 original files, 311,006,260 bytes of original expanded payload, under `CAT-review/`, plus notices outside that directory |
| GitHub automatic source archives | A snapshot of the Git tree; they do not include the Release-only runtime files |

The 33 omitted files are bundled runtime/dependency archives and metadata, **not newly generated execution outputs**. The full publication ZIP is a new wrapper preserving the individual original file bytes. Its checksum is therefore different from that of the original received ZIP.

Original received archive SHA-256:

```text
fad61f93e3915de81701d9ebe8f3326c8a66fbb23c1a16572ee8aac7609fa14f
```

Release assets are `CAT_v4_full_publication_bundle.zip`, the unchanged article and supplement PDFs, the compact article-source archive, and `SHA256SUMS`. [release-assets.json](release-assets.json) records their filenames, sizes, checksums, and download URLs. Asset checksums describe the actual asset files; the original archive hash above is retained separately as provenance. Use the full bundle for the supplied offline reproduction wrappers and original full-package manifest check.

The maintained [publication manifest](PUBLICATION_MANIFEST.json) describes this version directory. The published Release bundle and its embedded notices and manifest are frozen distribution records; subsequent maintenance of repository documentation does not rewrite them. The [fixed release recipe](../../../tools/release_cat_v4/README.md) documents how the existing assets are reproduced and verified.

## Scientific interpretation and verification

CAT is presented as an unrefereed research preprint. Its finite constructions use specified ranks, clocks, preparations, physical ports, and accessible carriers. Exact closure at a constrained port does not establish closure at every inward port. The common-source example is a prepared flat fixture, not a generic collapsing star. The readout protocol is a proposed experiment, not an observed gravitational signal.

The unresolved tasks include a consistent quantum theory across rank and clock sectors, realistic matter and gravity in a stable vacuum, widespread natural preparation of the required ports, and recovery at the evaporation endpoint. The companion guides retain these distinctions.

The recorded Version 3 technical review reran nine selected numerical drivers and ten selected Lean modules on Linux. The numerical comparison covers 59 groups and 1,195 floating-point values; the selected formal modules contain 365 theorem or lemma declarations. Version 4 inherits this execution evidence through source-identity comparisons and includes a successful limited package check with 143 finite-link systems. **No full numerical/Lean-suite rerun during the Version 4 review is asserted.** See [VERIFICATION.md](VERIFICATION.md) for exact scopes and [the original verification record](paper/evidence/verification.json).

Kernel-checked consequences retain their mathematical and physical inputs. They do not certify that the required ports, clocks, or instruments occur in nature. The archive includes negative results and unsuccessful preparations alongside successful conditional examples.

## Human contribution, AI, and rights

The manuscript identifies Yohtaro Soga's concepts, exact-closure criterion, and research direction. Codex assisted with mathematical construction, literature searches, numerical and Lean code, checks, and drafting; separate AI-generated technical reviews prompted changes. These reviews are development evidence, not journal peer review or independent human-expert acceptance. The [original contribution statement](paper/closing.tex) remains the source.

No new repository-wide license is assigned to the original CAT work. Existing third-party licenses and attribution requirements remain attached to their components. Read [RIGHTS.md](RIGHTS.md) and [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). The repository does not claim a DOI, journal acceptance, or an institution's endorsement.
