# Publication scope

This document defines the shared publication policy for the `physics` research repository and its GitHub Pages reading site. Each paper and version maintains its own distribution, provenance, scientific scope, and verification records.

## Repository and site

| Item | Value |
| --- | --- |
| Repository | [`gawakkyu0603-bit/physics`](https://github.com/gawakkyu0603-bit/physics) |
| Publication branch | `main` |
| Research hierarchy | Field → paper → version |
| Pages source | `main` branch, `/docs` directory |
| Pages base | <https://gawakkyu0603-bit.github.io/physics/> |
| English site entry | <https://gawakkyu0603-bit.github.io/physics/en/index.html> |
| Site catalog | [`site-src/catalog.json`](../site-src/catalog.json) |
| Site generator | [`tools/build_site.py`](../tools/build_site.py) |

The [repository README](../README.md) indexes physics fields and papers. A field README indexes its papers; a paper README explains that research and indexes its versions; a version README describes the corresponding materials, evidence, and reproduction instructions. A paper's version number is not a version number for the repository as a whole.

Public repository, field, paper, and version READMEs and the maintenance guide are maintained in English. Original research files retain their supplied language and content. Historical records retain their original wording where exact preservation is part of their provenance.

## Paper and version records

| Field | Paper | Version-specific publication record |
| --- | --- | --- |
| [Quantum gravity](../quantum-gravity/README.md) | [Correlation Actualization Theory](../quantum-gravity/correlation-actualization-theory/README.md) | [Version 4 scope, distribution, and provenance](../quantum-gravity/correlation-actualization-theory/v4/PUBLICATION_SCOPE.md) |

Add a record for each published version. Keep author identities, manuscript dates, release tags, original-file counts, archive sizes and hashes, figure counts, and scientific conclusions in the corresponding paper or version record. They do not apply automatically to other research in this repository.

The shared [coverage index](../site-src/COVERAGE.md) and [scientific QA index](../site-src/SCIENTIFIC_QA.md) link to the detailed companion-guide records for each paper and version.

## English reading guides

Each published paper provides three complete English guides:

| Audience | Required treatment |
| --- | --- |
| Research specialists | Technical definitions, assumptions, results, supporting evidence, and unresolved questions. |
| STEM students and graduates | Sufficient background and intermediate explanations to follow the paper and supplement. |
| General readers | Concrete explanations and figures that preserve the meaning and limits of the research. |

Every guide begins with a TL;DR and covers the full paper and supplement at its intended reader's level. Adapt vocabulary, equations, figures, and explanatory detail while preserving assumptions, data meanings, conclusions, negative results, and limitations. Complete topical coverage does not require reproducing every proof or every evidence file verbatim; the version-specific coverage table must show where each substantive topic is addressed and link to the original material.

Companion explanations do not alter the original research, create physical evidence, or turn conditional constructions or proposed experiments into observed results. Their scientific QA records distinguish content checks, executed calculations, inherited checks, and work that remains unverified.

## Version preservation and live pages

Store research as `field/paper/version/paper/`, with original files preserved inside the final `paper/` directory and publication documentation outside it. New versions receive new directories and namespaced tags. Preserve existing version directories, immutable release tags, original file bytes, and published Release assets; do not repurpose an old tag for a later revision.

The live reading site presents the version selected by the current catalog. Its paper URLs may later present a newer version. For reproducible citations, use the appropriate version directory at its immutable tag or exact commit, together with that version's Release assets and verification record. Maintain the earlier version's scope, coverage, and QA records when the live catalog advances.

A version's distribution record must distinguish original received archives, retained original files, publication wrappers, GitHub-generated source archives, and separately attached Release assets. State omitted payloads and their availability explicitly. Record file sizes and checksums for the files actually distributed; a new wrapper archive need not have the same checksum as the archive originally received. Publication manifests for maintained documentation and frozen Release manifests describe their respective distributions and must not be conflated.

## Verification, attribution, and rights

Report the scope and provenance of each check. A source-identity comparison can support inheritance of specified earlier checks; it is not a new execution of those checks. Separate mathematical assumptions and conditional results from physical hypotheses, experimental proposals, observations, and open problems. Automated checks and AI-assisted technical reviews do not establish journal peer review or independent human-expert acceptance.

Retain each paper's contribution statements, rights notices, and third-party licenses. Publishing a paper in this repository does not create a new blanket license for it. Do not infer a DOI, journal acceptance, or institutional endorsement from repository or Pages availability.

## Maintenance and search publication

Use [Adding research and publishing the site](../ADDING_PAPERS.md) for source organization, build commands, verification, versioned publication, and recorded registration status. The [site-source reference](../site-src/README.md) documents the generator and catalog.

Verify the repository, relevant tags and Release assets, Pages deployment, and live URLs before recording a publication as complete. Search ownership verification, sitemap retrieval, submission receipts, and actual search indexing are separate outcomes. A receipt alone does not establish that every URL is indexed. Ordinary builds and documentation updates do not authorize renewed registration, repeated submissions, scheduled monitoring, or recreation of removed ownership-verification files. Follow the recorded author decision for any outstanding search status, including the decision to wait on Google's sitemap status.
