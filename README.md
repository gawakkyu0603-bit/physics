# Physics

Versioned research manuscripts, reproducible evidence, and English reading guides for three audiences.

## Research library

The hierarchy is **field → paper → version**. Each version keeps its original research material separate from the explanatory website.

| Field | Paper | Version and evidence |
| --- | --- | --- |
| [Quantum gravity](quantum-gravity/README.md) | [Correlation Actualization Theory (CAT)](quantum-gravity/correlation-actualization-theory/README.md) | [Version 4](quantum-gravity/correlation-actualization-theory/v4/README.md) · [Verification](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) |

## Read CAT at your preferred level

Read the [English Pages home](https://gawakkyu0603-bit.github.io/physics/en/index.html). The public introductions are in English for all three audiences.

| Audience | English introduction |
| --- | --- |
| Research specialists | [Expert guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/expert.html) |
| STEM students and graduates | [Student guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/student.html) |
| General readers | [General guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/general.html) |

All three guides cover the paper's research themes and conclusions at the chosen level. The pages begin with a TL;DR, develop the full paper, and link to the original evidence and the other reading levels. They include eight figures for specialists, nine for students, and nine for general readers.

## Manuscript and distribution

CAT v4 is an **unrefereed research preprint** by Yohtaro Soga, dated 25 November 2026. It proposes irreversible gravitational receipts and changes of physical output domains. Its explicit results concern specified ranks, clocks, preparations, and ports. A theory connecting sectors, generic natural collapse, and endpoint recovery remain open.

The version directory retains **709 unchanged original files** under `paper/`. The full publication ZIP for the `cat-v4.0.0` [Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0) preserves all **742 original files**, including 33 bundled runtime/dependency files omitted from Git. Its distribution notices are outside the original `CAT-review/` payload. GitHub’s automatic source archives contain only the Git tree.

[Original article](quantum-gravity/correlation-actualization-theory/v4/paper/main.pdf) · [Supplement](quantum-gravity/correlation-actualization-theory/v4/paper/supplement.pdf) · [Reproduction instructions](quantum-gravity/correlation-actualization-theory/v4/README.md) · [Publication scope](docs/PUBLICATION_SCOPE.md)

The [verification record](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) separates v3 full-suite executions from v4 identity checks and limited reruns. The manuscript discloses the human author’s concepts and research direction, Codex assistance, and AI-generated technical reviews. Those reviews are not journal peer review.

## Adding research and building the site

Add future papers under their field and retain explicit version directories. Keep the supplied manuscripts immutable; put explanatory pages and their sources alongside the website workflow. Use [tools/build_site.py](tools/build_site.py) as the entry point for site generation. Each future paper receives exactly three English introductions: general, student, and expert. Every article starts with a TL;DR and explains the complete paper and supplement with enough detail for its intended readers. Public repository, field, paper, and version READMEs are maintained in English. Japanese maintenance notes remain available.

Follow the [paper addition, revision, and publication guide](ADDING_PAPERS.ja.md) (Japanese) for the complete maintenance workflow, including the three English reading guides, source coverage, verification, versioned releases, and Pages publication. The [site source reference](site-src/README.md) documents the catalog and content formats.

After all repository, Release, asset, and Pages publication work has finished and the public URLs have been verified, request discovery and indexing through Google Search Console and Bing Webmaster Tools, and notify Bing with IndexNow. Follow the relevant Google and Bing routes for Yahoo! JAPAN and international Yahoo Search. Record submission, receipt, crawling, and indexing separately. The [search submission and update guide](SEARCH_INDEXING.ja.md) (Japanese) documents these steps and their evidence.

No repository-wide license is newly assigned to the original research. Consult the version’s [rights statement](quantum-gravity/correlation-actualization-theory/v4/RIGHTS.md) and [third-party notices](quantum-gravity/correlation-actualization-theory/v4/THIRD_PARTY_NOTICES.md). No DOI or journal acceptance is asserted.

Repository: [gawakkyu0603-bit/physics](https://github.com/gawakkyu0603-bit/physics).
