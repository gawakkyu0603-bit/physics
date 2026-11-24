# Adding, revising, and publishing research papers

[Repository overview](README.md) · [Shared publication policy](docs/PUBLICATION_SCOPE.md) · [Site source reference](site-src/README.md)

This guide explains how to add future papers to the existing `physics` repository and publish their original materials, reproduction resources, and three English reading guides as a consistent collection. Every paper receives exactly three introductions: one for general readers, one for STEM students and graduates, and one for specialists. Public repository, field, paper, and version READMEs are maintained in English; do not create a separate Japanese README.

Keep supplied manuscripts unchanged and retain explicit version directories. Explanatory pages and their source files belong to the website workflow, whose build entry point is [tools/build_site.py](tools/build_site.py). The “stellar oscillations paper” used below is a fictional working example, not an existing research result or a claim of completed verification. Run commands from the repository root unless another working directory is explicitly shown.

## TL;DR

1. Identify the final supplied manuscript and preserve it under **field → paper → version → `paper/`**. Retain previous versions and record the hashes of the originals and distribution files.
2. Prepare field and paper READMEs and the version's verification, citation, rights, and distribution records. Register the version currently being presented in `site-src/catalog.json`.
3. Write **three English introductions for general readers, STEM students, and specialists**. Start every article with a TL;DR. Cover the paper and supplement's full arguments, conditions, proposed tests, and open problems at sufficient depth for that audience.
4. Check the correspondence between text, figures, equations, and sources. Place PDFs in `docs/downloads/`, extend the PDF hash checks for the new paper, and complete the build, structural checks, comparison with the original paper, and visual review.
5. Include original materials and generated `docs/` in the publication commit and publish it on `main`. Attach a paper-specific tag to the confirmed commit, then attach the distribution files to that tag's Release. GitHub Pages serves **the `/docs` directory on `main`**.
6. Verify the live URLs, links between the three English guides, PDFs, tag-pinned sources, and Release assets. For this initial publication, complete all repository, tag, Release asset, and Pages work before making the one-time initial submission through the relevant Google, Bing, and Yahoo routes. Submission receipts and actual search indexing are separate outcomes. Periodic monitoring and repeated submission are outside this request.

## 1. Publication destinations and version boundaries

Use the existing publication destinations. A separate repository is not required for each paper.

| Component | Setting in this repository |
| --- | --- |
| GitHub repository | [gawakkyu0603-bit/physics](https://github.com/gawakkyu0603-bit/physics) |
| Pages base URL | `https://gawakkyu0603-bit.github.io/physics/` |
| Published branch and directory | `main` / `docs` |
| Content registration | [site-src/catalog.json](site-src/catalog.json) |
| Site generator | [tools/build_site.py](tools/build_site.py) |
| Structural and link checks | [tools/verify_site.py](tools/verify_site.py) |

Manage versions of the original research separately from the current reading site. For example, original material can live at `stellar-physics/compact-star-modes/v1/paper/` while its expert guide is published at `en/stellar-physics/star-modes/expert.html`. **The current reading-page URLs do not contain a version number.** Multiple catalog entries with the same `field` and `slug` write to the same output paths.

Normally, keep only the version currently being presented for that paper in the catalog. For a revision, retain the original `v1/` directory, add `v2/`, and update the catalog's version, tag, source path, PDFs, and explanations together. Keep older versions accessible through the paper README, version directories, tags, and Releases. Serving older reading sites alongside the current one requires a separate URL design and corresponding generator and verifier changes. The current implementation does not automatically retain a separate website for every version.

### Choose names before adding files

| Purpose | Fictional example | Requirement |
| --- | --- | --- |
| Field, `field` | `stellar-physics` | Reuse an existing field when it already represents the subject. |
| Paper archive name, `archive_slug` | `compact-star-modes` | Match the paper's directory name within the field. |
| Pages paper name, `slug` | `star-modes` | Make it unique within the field. Changing it after publication changes the URLs. |
| Version, `version` | `"1"` | Use a string corresponding to the original-material directory `v1/`. |
| Release tag, `release` | `star-modes-v1.0.0` | Include the paper name to distinguish its tags from other papers' tags. |
| Content prefix, `content_prefix` | `star-modes-` | Use a distinct prefix for each paper. Do not reuse CAT's empty prefix. |

## 2. Inputs and working location

First confirm the final main paper, supplement, sources, data, execution instructions, author names, title, version, date, citation information, and distribution conditions. For checks already performed, retain records identifying the version, command, environment, inputs, results, failed examples, and unexecuted scope. If any information is missing, identify the gap; do not describe a check as executed or an input as obtained without evidence.

Check for outstanding work, then use a dedicated working branch. If there are existing changes, coordinate their disposition with their owner before switching branches.

```sh
git status --short
git switch main
git pull --ff-only origin main
git switch -c add-star-modes-v1
```

Keep large original archives, working copies of Release assets, and virtual environments outside the repository, for example in a sibling directory. This avoids accidentally adding duplicate distributions to Git. Files prepared for publication must not contain credentials or personal working notes.

## 3. Original materials and version documentation

For a new field, create `stellar-physics/README.md`. For the paper, create `stellar-physics/compact-star-modes/README.md`. Keep each README focused on its level of the hierarchy:

| README level | Purpose and content |
| --- | --- |
| Repository root | Introduce the research collection, index fields and papers, and link to the published site. List individual papers as entries; keep their detailed scientific descriptions, reading-guide tables, distribution counts, and research-status statements in their own paper directories. |
| Field | Introduce the subject area and index its papers and available versions. Link to each paper's overview for its detailed description and reading guides. |
| Paper | Present that paper's research question, author, scientific scope and limitations, three English reading guides, version list, and distribution links. Label details that apply only to a particular version. |
| Version | Document the exact manuscript version, reproduction instructions, verification evidence, citations, rights, and distribution contents. |

When adding a paper, update the root and field index entries and maintain the detailed overview in its paper directory. Do not turn the root or field README into the new paper's introduction. CAT's overview is maintained in [quantum-gravity/correlation-actualization-theory/README.md](quantum-gravity/correlation-actualization-theory/README.md). These READMEs are not generated by the site build. Build and publication procedures belong in this guide rather than the root README.

| Content of the version directory | What it records |
| --- | --- |
| `paper/` | Supplied manuscript, sources, data, and code. Do not change them to accommodate the explanations. |
| `README.md`, in English | Version contents, reading order, reproduction instructions, important files, and distribution links. |
| `VERIFICATION.md` | Facts checked for this version, evidence inherited from earlier versions, and work not executed for this version. |
| `PUBLICATION_SCOPE.md` | This version's identity, distribution and provenance, scientific limits, contribution statements, and links to its detailed records. |
| `reading-guides/COVERAGE.md` | Mapping from this version's main paper and supplement to the three English guides, with source locations and stable section IDs. |
| `reading-guides/SCIENTIFIC_QA.md` | Content comparisons, corrections, figure and equation checks, inherited evidence, and remaining unverified scope for this version's guides. |
| `RELEASE_NOTES.md` | Scope of the first release, or differences from the preceding version and publication changes. |
| `CITATION.cff` / `CITATION.bib` | Actual authors, title, version, publication date, and URL. Include a DOI only if one has been obtained. |
| `RIGHTS.md` / `THIRD_PARTY_NOTICES.md` | Verified rights and distribution conditions for the original research and third-party material. |
| `PUBLICATION_MANIFEST.json` | Correspondence with the originals, retained and omitted scope, and each version-directory file's size and SHA-256. |
| `release-assets.json` | Names, sizes, SHA-256 hashes, Release tag, and download locations of the actual assets to attach. |

Use the [CAT Version 4 directory](quantum-gravity/correlation-actualization-theory/v4/README.md) as a formatting reference. Establish original file counts, completed verification, authorship, licensing, AI involvement, review status, and hashes independently for every paper. Copying CAT's values or wording does not create evidence for another study.

Keep [docs/PUBLICATION_SCOPE.md](docs/PUBLICATION_SCOPE.md) as shared policy and an index of version-specific publication records. The shared [coverage index](site-src/COVERAGE.md) and [scientific QA index](site-src/SCIENTIFIC_QA.md) link to each version's detailed records. Add index entries for a new paper or version; put its findings, counts, hashes, and corrections in its own version directory. Maintain active publication and guide documentation in English. Preserve original research files and explicitly archived historical evidence in their original wording and language.

If some original materials are excluded from Git, identify their paths, the reason, and whether the complete distribution includes them. Use file counts and hashes to make the exact scope of identity between originals and distributions traceable. If a manuscript needs correction, treat it as a new version and record the changes.

Do not assign a new repository-wide license to the original research merely by adding it here. Preserve each paper and version's own applicable rights and third-party notices. For CAT v4, see its [rights statement](quantum-gravity/correlation-actualization-theory/v4/RIGHTS.md) and [third-party notices](quantum-gravity/correlation-actualization-theory/v4/THIRD_PARTY_NOTICES.md); these are references for CAT, not terms to copy to another paper. Do not imply a DOI or journal acceptance without the corresponding evidence.

## 4. Register the field and paper in the catalog

Add entries to `site-src/catalog.json` while retaining the existing entries. Keep top-level `languages` as `["en"]` and set each paper's `languages` to `["en"]` as well. For a new field, add an entry of this form to the `fields` array:

```json
{
  "slug": "stellar-physics",
  "name": {"en": "Stellar physics"},
  "summary": {
    "en": "Papers and explanations on stellar structure and oscillations."
  }
}
```

The following is a minimal example for the `papers` array. Replace the title, author, date, and descriptions with the actual new paper's information.

```json
{
  "slug": "star-modes",
  "field": "stellar-physics",
  "archive_slug": "compact-star-modes",
  "title": "Example paper title",
  "subtitle": "Example descriptive subtitle",
  "author": "Author name",
  "version": "1",
  "date": "YYYY-MM-DD",
  "release": "star-modes-v1.0.0",
  "source_path": "stellar-physics/compact-star-modes/v1/paper",
  "content_prefix": "star-modes-",
  "main_pdf": "downloads/star-modes-v1-main.pdf",
  "supplement_pdf": "downloads/star-modes-v1-supplement.pdf",
  "audiences": ["general", "student", "expert"],
  "languages": ["en"],
  "summary": {
    "en": "The actual research question and the scope of the results."
  }
}
```

`source_path` is relative to the repository root; PDF paths are relative to `docs/`. The verification link at the end of an article is assembled from `field/archive_slug/vVERSION/VERIFICATION.md`, so these values must also match the files' actual locations. Retain the existing `public_base_url`, including its trailing `/physics/`.

For informative navigation, add verified values for `short_title`, `page_counts`, `audience_descriptions`, `reading_times`, and `scope`. See the [site source reference](site-src/README.md) for the complete format and behavior when optional values are omitted. Base page counts and reading-time estimates on the actual manuscript and explanations. Register a figure before naming it in `hero_figure`.

Check the generator's publication-status and contribution statements against the new paper. The current header label `Research preprint` and catalog-footer wording about preprints and AI contributions are fixed template strings, not catalog fields. If they do not apply, adapt the templates to represent each paper and the collection accurately before publishing. Do not infer those facts from CAT's existing presentation.

The current shared interface assumes two PDFs: a main paper and a supplement. To support a paper without a supplement, first adapt the interface, builder, and verifier instead of pointing to an empty or unrelated PDF. The `interactive_return` feature explains CAT's ideal return behavior for two groups. For another paper, normally omit it or set it to `false`; assess it separately only if its mathematical content is actually relevant.

## 5. Prepare three English guides

The prefix in the example corresponds to these three source fragments. Prepare all three for future papers as well.

| Audience | English source fragment |
| --- | --- |
| General readers | `site-src/content/star-modes-general-en.html` |
| STEM students and graduates | `site-src/content/star-modes-student-en.html` |
| Specialists | `site-src/content/star-modes-expert-en.html` |

**Write three English explanations that allow readers to understand the whole paper.** Before drafting, inventory every section of the main paper and supplement, principal definitions, assumptions, results, comparisons, proposed tests, counterexamples or failure conditions, and limitations. Organize these into a readable progression from introduction to conclusion for each audience.

| Audience | Background and depth | Equations and figures |
| --- | --- | --- |
| General readers | Aim for the level of a science magazine such as *Newton*. Explain the research question, concrete examples, mechanisms, and meaning of the results in sequence. Define necessary terms in the text. | Where an equation is needed, explain its symbols and meaning in words. Emphasize diagrams and concrete numerical examples, and distinguish analogies from physical claims. |
| STEM students and graduates | Bridge undergraduate mathematics and physics to the paper's specific definitions and tools. Include intermediate steps and worked calculations. | Explain basic equations, units, assumptions, and limits, and connect the values shown in figures with the calculations. |
| Specialists | Treat definitions, conditions of theorems or claims, essential derivations, differences from existing theory, and reproduction methods precisely. | Identify correspondence with the paper's notation, equation numbers, numerical conditions, sources, code, and evidence. |

All three levels must cover the research themes, conditions, conclusions, limitations, and sources, with numerical values and figures retaining their meaning in the original paper. Changing explanatory depth must not turn a conditional result into an unconditional claim. Use natural, readable English. Do not impose an arbitrary length cap: provide the explanation needed to bridge the audience's prior knowledge to the argument. Use paragraphs, sections, and a table of contents to organize longer material.

### Retain a coverage and source map

Create `reading-guides/COVERAGE.md` within the new paper's version directory, with a mapping table containing at least the columns below. For the working example, use `stellar-physics/compact-star-modes/v1/reading-guides/COVERAGE.md`. Check each topic individually so that omissions remain visible, then add a link in the shared [coverage index](site-src/COVERAGE.md).

| Original location | Topic and conditions | General EN | Student EN | Expert EN | Supporting evidence |
| --- | --- | --- | --- | --- | --- |
| Main-paper section or equation number; supplement section | What is explained and what is assumed | Section ID | Section ID | Section ID | PDF page, source, data, or execution record |

A statement that “everything is covered” is insufficient. Use the table to check supplementary results, validation plans, negative results, and open questions. Record this version's content comparisons, corrections, and unverified scope in its own `reading-guides/SCIENTIFIC_QA.md`, and link it from the shared [scientific QA index](site-src/SCIENTIFIC_QA.md). Check numerical values and annotations within figures with the same care as the prose. Keep earlier versions' records when the catalog advances; do not append a new paper's evidence to CAT's records or replace an older version's record with the new one.

## 6. Format article text, equations, and source links

A source fragment contains one `article`, not a complete HTML page. This example illustrates the format only:

```html
<article lang="en">
  <header class="article-header">
    <h1>A guide for this audience</h1>
    <p class="lead">Introduce the background and the research question.</p>
  </header>
  <aside class="tldr" id="star-modes-student-tldr">
    <h2>TL;DR</h2>
    <p>State the question, results, conditions, and open problems.</p>
  </aside>
  <section id="star-modes-student-model">
    <h2 id="star-modes-student-model-heading">Model and conditions</h2>
    <p>Define the notation, then explain the equations and examples.</p>
    <div data-figure="star-modes-student-overview"></div>
    <p><a href="{{PAPER_PDF}}#page=2">Relevant page in the paper</a></p>
    <p><a href="{{SUPP_PDF}}#page=3">Relevant page in the supplement</a></p>
    <p><a href="{{SOURCE_ROOT}}/main.tex">Original source file</a></p>
  </section>
</article>
```

The builder moves the TL;DR to the start of the article body, places the title in the common page header, and generates a table of contents from `h2` headings. Keep IDs unique within each page. Common navigation links to the paper's other reading levels and landing page are generated automatically. Check the actual destinations of manually written body links as well.

`{{PAPER_PDF}}` and `{{SUPP_PDF}}` become links to the served PDFs; `{{SOURCE_ROOT}}` becomes a GitHub link to the original material pinned to the catalog's Release tag. Replace the example's page numbers and filenames using the actual manuscript. Do not leave a nonexistent `main.tex` or a page number from another version.

Use `\(...\)` for inline mathematics and `<div class="equation">\[...\]</div>` for displayed equations. Introduce symbols and state units and validity conditions nearby. Break complex expressions into parts whose meaning can be followed. Check that long equations remain readable on narrow screens. Encode inequality characters in HTML as `&lt;` / `&gt;` when necessary. Compare displayed equations with the original paper and correct any KaTeX conversion errors before proceeding.

## 7. Create colorful, accurate figures and tables

Add a named function to [site-src/figures.py](site-src/figures.py) that accepts `lang` and returns the SVG's inner markup and its height. The current common width is 880. Existing drawing helpers are available; embed the figure in article text by its figure ID.

```python
# Define star_modes_overview(lang) before registering it.
MAP['star-modes-student-overview'] = star_modes_overview
CAPTIONS['star_modes_overview'] = {
    'en': {
        'title': 'English figure title',
        'description': 'English explanation with conditions, units, sources, and scope.'
    }
}
```

The key in `MAP` corresponds to the article's `data-figure` value; the key in `CAPTIONS` is the **function name**. The figure API accepts the English dictionary above. For compatibility with existing figures, it also accepts a four-element tuple, using the second element for the English title and the fourth for the English description. The function receives `lang="en"`. Shared processing adds an SVG title and a caption. Generated figure IDs use `figure-` followed by the figure ID. Reusing the same figure ID twice on a page produces duplicate IDs; register a distinct ID for a repeated appearance.

Place mechanism diagrams, quantity comparisons, process diagrams, and tables connecting conditions to results where they resolve likely reader difficulties. Their purpose is to advance the explanation. Pair colors with English labels or line styles, and keep values, arrangements, and color meanings consistent with the text.

For computed plots, retain traceable source data and processing, and identify axes, units, parameters, errors, and scope. Distinguish schematic diagrams, assumed models, calculations, and observations. Do not present an unperformed experiment or unverified prediction as an observed result.

## 8. Place PDFs and extend identity checks

The builder does not copy PDFs. Place the final originals' bytes at `docs/downloads/star-modes-v1-main.pdf` and `docs/downloads/star-modes-v1-supplement.pdf`. If the same PDFs are distributed in the original-material directory, Pages, and Release assets, verify matching SHA-256 hashes across all three locations.

The example below assumes the original files are `paper/main.pdf` and `paper/supplement.pdf`. Substitute actual paths if the filenames differ.

```python
from pathlib import Path
import hashlib

pairs = [
    ('stellar-physics/compact-star-modes/v1/paper/main.pdf',
     'docs/downloads/star-modes-v1-main.pdf'),
    ('stellar-physics/compact-star-modes/v1/paper/supplement.pdf',
     'docs/downloads/star-modes-v1-supplement.pdf'),
]
for original, served in pairs:
    expected = hashlib.sha256(Path(original).read_bytes()).hexdigest()
    actual = hashlib.sha256(Path(served).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'PDF differs: {served}')
    print(served, Path(served).stat().st_size, actual)
```

The `expected` dictionary in the current `tools/verify_site.py` contains the two CAT Version 4 PDFs. **Adding a paper to the catalog does not automatically add hash checks for its PDFs.** Add the new PDFs' independently obtained hashes to the verifier and retain the existing CAT checks. If this mechanism is generalized later, record expected values independently from verified originals; do not regenerate expected values from the files being tested on every verification run.

## 9. Build, then check structure, content, and presentation

### 9.1 Generate the site and run structural checks

Have Node.js, npm, and Python 3 available. If using a virtual environment, create it outside the repository: do not assume the current `.gitignore` excludes an arbitrary environment directory name.

```sh
python3 -m venv ../physics-site-venv
. ../physics-site-venv/bin/activate
python3 -m pip install -r site-src/requirements.txt
npm ci
python3 tools/build_site.py
python3 tools/verify_site.py
git diff --check
git diff --stat
```

`npm ci` installs dependencies from the lockfile. `npm run build` and `npm run verify` correspond to the Python commands above. The build updates HTML, `docs/sitemap.xml`, and `site-src/build-stats.json`, and ensures the Pages `.nojekyll` marker exists. Verification updates `site-src/verification.json`. Ownership-verification files are managed separately: the builder preserves existing Google and Bing files and does not generate or restore an IndexNow key file. Keep a deliberately removed verification file removed unless its restoration is requested. Place or update served CSS, JavaScript, fonts, and other assets separately when needed.

Confirm an exit code of 0 and `error_count` of 0. Checks cover local files and anchors, original-source paths, IDs, the opening TL;DR, KaTeX, configured publication languages and articles, registered PDF hashes, canonical URLs, hreflang links including English self-references, and sitemap URL scope. For the current single paper, the sitemap covers seven HTML pages and two PDFs: nine URLs in total. When adding papers, use counts appropriate to the actual published content.

The GitHub source-link check here verifies the existence of corresponding **local files**. Separately check whether the remote tag exists and whether its public files can be retrieved. Page counts increase as papers are added, so the CAT-only counts are not permanent success criteria.

### 9.2 Compare the explanations with the original paper

Read all three English guides while comparing the original paper, supplement, and coverage table. Check assumptions, equations, values, units, figures, sources, and conditional conclusions. Recalculate worked examples added to the explanations and label them as explanatory examples. Passing structural checks does not establish scientific correctness, completeness, or sufficient explanation for the intended audience.

### 9.3 Read the site on desktop and narrow screens

```sh
python3 -m http.server 8000 --directory docs
```

Starting at `http://localhost:8000/`, open the English home, field page, paper landing page, and all three reading guides. Inspect line length, paragraphs, headings, the table of contents, equations, tables, figure text, horizontal scrolling, navigation between reading levels, and links to PDFs and original sources. Read the general guide from a first-time reader's perspective and check whether a specialist can follow claims back to their evidence.

Removing or renaming a catalog entry does not automatically delete its old generated HTML. When a URL changes, decide whether to retain the old page or provide a navigation page, and check explicitly that outdated content is not still being served unintentionally. Also verify that the diff contains no unintended changes to the original paper.

## 10. Finalize Release assets and manifests

GitHub's automatic source archives differ from distributions assembled for an individual paper. Automatic `Source code (zip)` and `Source code (tar.gz)` archives contain the entire repository at the tag. In a multi-paper repository, this includes other papers' Git files. The archives do not add runtimes or other materials omitted from Git. See GitHub's [Release documentation](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases).

For a distribution organized like CAT's, prepare these five assets. Describe their actual contents and filenames in the version README according to the paper's needs.

| Asset | Purpose |
| --- | --- |
| Main-paper PDF | Final reading copy, identical to the PDF served by Pages. |
| Supplement PDF | Derivations, validation, and additional material supporting the paper. |
| Article-source `tar.gz` | The actual sources required to rebuild the paper. |
| Complete distribution ZIP | All original materials and necessary reproduction resources; state whether it contains materials omitted from Git. |
| `SHA256SUMS` | Hashes of the distribution files above; do not include this checksum file itself in its own list. |

Create `PUBLICATION_MANIFEST.json` from the new version's actual contents, using the [existing CAT format](quantum-gravity/correlation-actualization-theory/v4/PUBLICATION_MANIFEST.json) as a reference. Paths are relative to the version directory, and the manifest excludes itself. If a version-directory README or another wrapper changes, update its recorded hash. Separately record the completed assets' sizes, hashes, and URLs in `release-assets.json`. These two records describe different sets of files.

After publication, the manifest on `main` may be maintained to describe that version directory's current documentation. Preserve the original-file hashes and any frozen manifest embedded in an existing Release asset. Adding or correcting repository documentation does not require rebuilding published assets or moving an existing tag. State which distribution each manifest describes.

The current site generation commands do not automatically ingest original materials or create a distribution ZIP, source archive, manifest, or Release. Complete those tasks before fixing the publication commit. Inspect archive paths, extracted file lists, and correspondence with original hashes; successful compression alone does not establish completeness.

For example, if assets are prepared in `../star-modes-release-assets/`, create checksums as follows. Use the actual filenames.

```sh
(
  cd ../star-modes-release-assets || exit 1
  sha256sum star-modes-v1-main.pdf star-modes-v1-supplement.pdf \
    star-modes-v1-source.tar.gz star-modes-v1-full-bundle.zip > SHA256SUMS
  sha256sum --check SHA256SUMS
)
```

## 11. Publish Git changes, tags, Releases, and Pages

### 11.1 Review the changes and merge into main

On the same working branch, review the added originals, explanations, catalog, article fragments, figures, verification code, and generated output. The following explicitly stages an example set of paths; adjust it to the actual changes.

```sh
git add stellar-physics README.md site-src tools/verify_site.py docs
git diff --cached --stat
git diff --cached --check
git commit -m "Add star modes v1 paper and three English reading guides"
git push -u origin add-star-modes-v1
```

If the builder or other files also changed, stage those changes explicitly. Create a pull request from this branch to `main` on GitHub. Confirm that the original materials, explanations, distribution records, and generated files agree, then merge. Once the publication content is fixed, update the local `main`:

```sh
git switch main
git pull --ff-only origin main
git status --short
git rev-parse HEAD
```

Record the displayed commit in the verification and publication records. Do not tag while intended publication changes remain uncommitted or unmerged.

### 11.2 Tag the confirmed commit for this paper

This example creates a new tag; it is not a procedure for moving or replacing an existing tag. CAT's published `cat-v4.0.0` tag is immutable and must not be moved when adding another paper or maintaining the site.

```sh
paper_tag=star-modes-v1.0.0
paper_publication_commit=$(git rev-parse HEAD)
git tag -a "$paper_tag" "$paper_publication_commit" -m "Star modes version 1"
git push origin "refs/tags/$paper_tag"
```

Use the same tag as the catalog. Record later corrections in history and create an appropriate new version or distribution-revision tag. If only the explanations of the same manuscript version are improved, retain the manuscript, record the reason and scope of the changes, and update the reading pages on `main`.

### 11.3 Create the Release and attach assets

Use either GitHub's interface or an authenticated GitHub CLI. Verify the asset contents and tag before running a command such as:

```sh
gh release create star-modes-v1.0.0 \
  --repo gawakkyu0603-bit/physics \
  --verify-tag \
  --latest=false \
  --title "Star modes — version 1" \
  --notes-file stellar-physics/compact-star-modes/v1/RELEASE_NOTES.md \
  ../star-modes-release-assets/star-modes-v1-main.pdf \
  ../star-modes-release-assets/star-modes-v1-supplement.pdf \
  ../star-modes-release-assets/star-modes-v1-source.tar.gz \
  ../star-modes-release-assets/star-modes-v1-full-bundle.zip \
  ../star-modes-release-assets/SHA256SUMS
```

`--verify-tag` aborts creation if the remote tag does not exist. `--latest=false` prevents this Release from being marked as the repository-wide “Latest.” In a multi-paper repository, identify each paper's current version through its catalog, index, and tags rather than relying solely on a global Latest label. See the [GitHub CLI manual](https://cli.github.com/manual/gh_release_create) for the options.

### 11.4 Confirm the Pages source

In **Settings → Pages → Build and deployment**, set Source to **Deploy from a branch**, Branch to **main**, and Folder to **/docs**. If this is already configured, no per-paper reconfiguration is needed. After publishing generated `docs/` on `main`, confirm the Pages deployment result. A successful local build is not a completed publication. See the [official GitHub Pages configuration instructions](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site).

During publication, Pages may update before the tag or Release exists. Do not report the publication as complete until every publication destination has been checked.

## 12. Verify the live publication and make the initial submission

Navigate from the public site home to the new field and paper, and open all three English guides. Check the live URLs rather than relying on a cached page or local preview.

- Each article begins with a TL;DR, and navigation to other reading levels, PDFs, and original sources works.
- The Release tag identifies the recorded commit, every attached asset is retrievable, and downloaded assets can be checked against `SHA256SUMS`.
- Pages PDFs match the originals, and the tag-pinned original-material and verification links work publicly.
- `https://gawakkyu0603-bit.github.io/physics/sitemap.xml` contains the new HTML and registered PDFs, and canonical and English hreflang URLs correspond to live pages.
- The README research index, paper version list, Release, and Pages all identify the same version.

For this initial publication, finish and verify all repository, tag, Release asset, and Pages work before the initial registration and sitemap submission through Google Search Console and Bing Webmaster Tools, and the IndexNow notification to Bing. Yahoo! JAPAN uses the relevant Google route; international Yahoo Search uses the Bing Webmaster Tools route. Use ownership-verification values actually issued by the service. Distinguish submission and receipt from inclusion in search results. This request does not include periodic monitoring, automatic retries, or repeated submissions. An initial step already completed should not be repeated merely because this guide is being maintained.

On 25 November 2026, the author reported completion of Google Search Console registration and Bing Webmaster Tools setup. Google's submitted sitemap had shown "Couldn't fetch", but the author subsequently opened the sitemap from the Search Console link and chose to wait for the status to settle. Follow that decision without further submission, automatic retries, or scheduled monitoring. Opening the link confirms access through that link; it does not establish successful retrieval by Google's sitemap processor or completed indexing. A temporary service issue remains a possibility, not a confirmed diagnosis.

The initial IndexNow submission for nine URLs received HTTP 202 at 07:31 JST that day ([workflow run 45501701597](https://github.com/gawakkyu0603-bit/physics/actions/runs/45501701597)), indicating receipt with key validation pending. The author later removed the public IndexNow verification file in [commit 88a042c](https://github.com/gawakkyu0603-bit/physics/commit/88a042cb9523e409408952ef033439e16da56cac). Ordinary builds respect that removal. `site-src/indexnow.json` retains the earlier manual-submission configuration; it does not cause the file to be regenerated or a notification to be sent. The manual submission script requires a matching local and live key file before it can send a notification. These historical records do not establish indexing of every URL, and documentation changes do not require a new submission.

### Ownership files with the main /docs Pages source

Register the project URL `https://gawakkyu0603-bit.github.io/physics/` as the site to verify. Bing permits verification of a site branch, as described in its [official site verification help](https://www2.bing.com/webmasters/help/add-and-verify-site-12184f8b). Because Pages serves `docs/` on `main`, place service-issued Google and Bing ownership-verification files inside `docs/`. Their filenames then appear directly under the project's public URL, without `docs/` in the URL. A file placed only at the repository root is not served by this Pages configuration.

For example, the existing Google file is placed at `docs/google0dbfbd45bd34f75a.html` and served at `https://gawakkyu0603-bit.github.io/physics/google0dbfbd45bd34f75a.html`. Bing's `BingSiteAuth.xml` is stored at `docs/BingSiteAuth.xml`; its public URL is `https://gawakkyu0603-bit.github.io/physics/BingSiteAuth.xml`. Use the original filename and exact contents supplied for the correct site and account; do not invent a token or XML body. When adding a verification file, commit it, wait for the Pages deployment to succeed, and confirm its public URL before choosing Verify in the service. Preserve verification files when rebuilding the site. Ownership verification and actual search indexing remain separate outcomes.

## 13. Completion records and the next handoff

Record the following in the paper's existing publication records to avoid confusion during later revisions. Keep reproduction commands and verification logs at paths a future maintainer can access.

| Record | Information to retain |
| --- | --- |
| Paper identity | Title, authors, field, `archive_slug`, `slug`, manuscript version, and date. |
| Originals and retained scope | Original archive SHA-256, counts and paths of retained and excluded files, and correspondence with the complete distribution. |
| Published locations | Confirmed `main` commit, paper-specific tag, Release URL, English paper landing page, and the three guide URLs. |
| Build and mechanical checks | Commands, environment, exit codes, verification-record paths, and PDF hashes. |
| Content and presentation review | Coverage table, comparison with the original paper, figure/equation/source checks, and desktop and narrow-screen review. |
| Verification scope | What was executed now, what relies on evidence from prior versions, and what remains unchecked. |
| Distribution | Actual attached filenames, sizes, SHA-256 hashes, and download-verification results. |
| This initial submission | Destination service, submission time, and actual response. Do not treat receipt alone as proof of indexing. |
| Remaining work | Identify remaining research questions and remaining publication tasks separately. |

Before adding the next paper, read these records and the [site source reference](site-src/README.md). If the code has changed, reconcile it with the instructions. Retain earlier papers' original materials and published tags while adding new materials, explanations, and distributions.
