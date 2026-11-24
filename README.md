# Physics

Versioned research manuscripts, reproducible evidence, and Japanese/English reading guides.

English · [日本語](README.ja.md)

## Research library

The hierarchy is **field → paper → version**. Each version keeps its original research material separate from the explanatory website.

| Field | Paper | Version and evidence |
| --- | --- | --- |
| [Quantum gravity](quantum-gravity/README.md) | [Correlation Actualization Theory (CAT)](quantum-gravity/correlation-actualization-theory/README.md) | [Version 4](quantum-gravity/correlation-actualization-theory/v4/README.md) · [Verification](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) |

## Read CAT at your preferred level

The Pages home is [English](https://gawakkyu0603-bit.github.io/physics/en/index.html) or [日本語](https://gawakkyu0603-bit.github.io/physics/ja/index.html).

| Audience | English | 日本語 |
| --- | --- | --- |
| Research specialists | [Expert guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/expert.html) | [専門家向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/expert.html) |
| STEM students and graduates | [Student guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/student.html) | [理工系学生向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/student.html) |
| General readers | [General guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/general.html) | [一般読者向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/general.html) |

Each language pair covers the same research themes and conclusions. The pages begin with a TL;DR, develop the full paper at the chosen level, and link to the original evidence. The pages include eight figures for specialists, nine for students, and nine for general readers, with corresponding figures in both languages.

## Manuscript and distribution

CAT v4 is an **unrefereed research preprint** by Yohtaro Soga, dated 25 November 2026. It proposes irreversible gravitational receipts and changes of physical output domains. Its explicit results concern specified ranks, clocks, preparations, and ports. A theory connecting sectors, generic natural collapse, and endpoint recovery remain open.

The version directory retains **709 unchanged original files** under `paper/`. The full publication ZIP for the `cat-v4.0.0` [Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0) preserves all **742 original files**, including 33 bundled runtime/dependency files omitted from Git. Its distribution notices are outside the original `CAT-review/` payload. GitHub’s automatic source archives contain only the Git tree.

[Original article](quantum-gravity/correlation-actualization-theory/v4/paper/main.pdf) · [Supplement](quantum-gravity/correlation-actualization-theory/v4/paper/supplement.pdf) · [Reproduction instructions](quantum-gravity/correlation-actualization-theory/v4/README.md) · [Publication scope](docs/PUBLICATION_SCOPE.md)

The [verification record](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) separates v3 full-suite executions from v4 identity checks and limited reruns. The manuscript discloses the human author’s concepts and research direction, Codex assistance, and AI-generated technical reviews. Those reviews are not journal peer review.

## Adding research and building the site

Add future papers under their field and retain explicit version directories. Keep the supplied manuscripts immutable; put explanatory pages and their sources alongside the website workflow. Use [tools/build_site.py](tools/build_site.py) as the entry point for site generation, and maintain equivalent Japanese and English coverage.

No repository-wide license is newly assigned to the original research. Consult the version’s [rights statement](quantum-gravity/correlation-actualization-theory/v4/RIGHTS.md) and [third-party notices](quantum-gravity/correlation-actualization-theory/v4/THIRD_PARTY_NOTICES.md). No DOI or journal acceptance is asserted.

Repository: [gawakkyu0603-bit/physics](https://github.com/gawakkyu0603-bit/physics).
