# Publication scope

This repository publishes physics research papers, their sources and supporting materials, and English reading guides. The [research index](../README.md) leads to each paper's overview and available files.

## Repository and reading site

| Location | Purpose |
| --- | --- |
| [GitHub repository](https://github.com/gawakkyu0603-bit/physics) | Manuscripts, sources, data, code, citation information, and rights notices, organized by field and paper. |
| [Physics reading site](https://gawakkyu0603-bit.github.io/physics/en/index.html) | A general research index leading to individual paper pages. |
| Each paper's reading page | The latest published manuscript's introduction, available downloads, and three English reading guides. |

GitHub Pages serves the `docs/` directory on `main`. The [catalog](../site-src/catalog.json) identifies the published papers and their resources. The site displays only the latest published version of each paper; earlier materials may remain on GitHub for reproducible citations. Paper-specific figures and explanations belong on that paper's pages.

## Public descriptions and resources

Repository and field READMEs are research indexes. A paper README explains its question, scope, available materials, and reading options. A version directory provides the corresponding source files, practical reproduction instructions, citation details, and rights notices.

Public descriptions focus on the research and its use. Internal review correspondence, issue-resolution checklists, and revision chronology are not part of the public presentation. State scientific assumptions, limitations, and the actual status of the work where they help readers interpret it.

Each paper supplies the resources appropriate to that work. A supplement, a complete runtime bundle, formal-verification code, or a GitHub Release is optional. Do not imply that an absent resource is available or apply one paper's authorship, contribution history, or publication status to another.

## Three English reading guides

Each paper has guides for **general readers**, **STEM students and graduates**, and **specialists**. Every guide begins with a TL;DR and explains the complete paper and any accompanying supplement at its intended reader's level. Adapt the vocabulary, equations, and explanatory detail while retaining the research's assumptions, conclusions, and open questions.

Public documentation is maintained in English. Original research files retain their supplied language. Keep physical hypotheses, conditional mathematical results, proposed experiments, and observations distinguishable.

## Sources, citation, and rights

Keep original research and published distributions identifiable. Use a version directory, release tag, or exact commit when citing a particular distribution. Fixed tags and Release assets identify their original contents; later website maintenance does not revise those distributions unless the author explicitly withdraws the work.

Each paper retains its own contribution statements, rights, and third-party notices in its research materials. Inclusion in this repository does not create a blanket license or imply journal acceptance.

For adding papers, building the site, and publishing updates, use [ADDING_PAPERS.md](../ADDING_PAPERS.md). The [site source reference](../site-src/README.md) describes the catalog and generator.

The public templates do not display internal version numbers or review-related metadata by default. Version identifiers remain available where needed for precise source paths and citation. The canonical site map is `sitemap.xml`.

## Current-manuscript publication

The OSTQD series presents only the current manuscript of each study. Replace contents in stable source directories, retain existing PDF and reading-page URLs, and remove superseded source files from the current tree. Existing source-path names are retained for link compatibility, not displayed as version labels. Ordinary Git history is not rewritten. The scientific reading order is independent of manuscript updates.
