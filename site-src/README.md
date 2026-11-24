# Site source reference

[Repository overview](../README.md) · [Publication policy](../docs/PUBLICATION_SCOPE.md) · [Adding and publishing papers](../ADDING_PAPERS.md)

This directory contains the catalog, article fragments, figure definitions, and rendering support for the English research reading site. Research materials follow **field → paper → version**; the catalog chooses the version currently presented on the site. Each paper has exactly three English guides: general, student, and expert. Every guide begins with a TL;DR and covers the main paper and supplement at an appropriate depth for its audience.

Use [ADDING_PAPERS.md](../ADDING_PAPERS.md) for the complete publication workflow. This reference describes the source formats, generated outputs, and current implementation limits. Active publication documentation is maintained in English. Original research files and explicitly archived historical evidence retain their original wording and language.

## 1. Sources, records, and outputs

| Location | Role |
| --- | --- |
| [catalog.json](catalog.json) | Public base URL, fields, papers, selected versions, article registration, and PDF paths. |
| `content/` | Three English HTML fragments **per paper**, identified by that paper's content prefix. |
| [figures.py](figures.py) | SVG drawing functions, figure IDs, and English captions. |
| [render-math.cjs](render-math.cjs) | KaTeX rendering into HTML and MathML. |
| [COVERAGE.md](COVERAGE.md) | Shared index of version-specific source-to-guide coverage records. |
| [SCIENTIFIC_QA.md](SCIENTIFIC_QA.md) | Shared index of version-specific scientific content checks and corrections. |
| [../tools/build_site.py](../tools/build_site.py) | Common navigation, contents lists, figures, mathematics, catalog pages, and sitemap generation. |
| [../tools/verify_site.py](../tools/verify_site.py) | Structural, link, language, PDF identity, canonical, hreflang, and sitemap checks. |
| `../docs/` | Generated HTML and separately maintained PDFs, CSS, JavaScript, fonts, and ownership files. |
| [build-stats.json](build-stats.json) / [verification.json](verification.json) | Records updated by the build and verification commands. |

Detailed coverage and QA records belong under each version's `reading-guides/` directory. The shared Markdown files above are indexes; a new paper receives its own records. For the current CAT Version 4 example, see [coverage](../quantum-gravity/correlation-actualization-theory/v4/reading-guides/COVERAGE.md), [scientific QA](../quantum-gravity/correlation-actualization-theory/v4/reading-guides/SCIENTIFIC_QA.md), and [publication scope](../quantum-gravity/correlation-actualization-theory/v4/PUBLICATION_SCOPE.md).

The builder writes HTML, `docs/sitemap.xml`, and `build-stats.json`, and ensures that `docs/.nojekyll` exists. It does not copy PDFs, CSS, JavaScript, or fonts into place. Those assets must already be at the configured paths.

Search URLs come from `catalog.json`'s `public_base_url`, which ends in `/`. The sitemap lists generated HTML and the registered main-paper and supplement PDFs. Pages have absolute self-referencing canonical URLs. The shared entry and English index advertise `en` and `x-default` alternates; other English pages advertise their English self-reference.

Ownership files are maintained separately from generation. The builder preserves existing service-issued Google and Bing files and does not generate or restore an IndexNow key file. [indexnow.json](indexnow.json) retains the earlier manual-submission configuration. The manual submission script requires a matching local and live key file; leaving the public key file absent prevents a new notification. A normal build sends no search notifications. Initial registration status and the author's decision to wait on Google's sitemap status are recorded in [the publication guide](../ADDING_PAPERS.md#12-verify-the-live-publication-and-make-the-initial-submission); no periodic monitoring or automatic retries are configured by this workflow.

## 2. Research paths and the selected version

These fictional names illustrate the path relationships; they do not identify an existing paper or verification result.

| Item | Example |
| --- | --- |
| Field directory | `stellar-physics/` |
| Paper archive directory | `stellar-physics/compact-star-modes/` |
| Version directory | `stellar-physics/compact-star-modes/v1/` |
| Original manuscript, code, and evidence | `stellar-physics/compact-star-modes/v1/paper/` |
| Version publication record | `stellar-physics/compact-star-modes/v1/PUBLICATION_SCOPE.md` |
| Guide coverage and QA | `stellar-physics/compact-star-modes/v1/reading-guides/` |
| Release tag | `star-modes-v1.0.0` |
| Pages paper path | `en/stellar-physics/star-modes/` |

Keep supplied original files unchanged. Version-specific READMEs, provenance, verification, rights, and guide records live outside the original `paper/` directory. If some original runtime files are omitted from Git, record their paths and how they are included in the complete distribution.

A revision adds a new version directory, such as `v2/`, while retaining the earlier version and immutable release tag. Current Pages URLs do not include a version number. Two catalog entries with the same `field` and `slug` write to the same HTML paths; select one current version per paper. Earlier research versions remain accessible through their directories, tags, and Releases. Companion-guide maintenance on `main` does not rewrite frozen Release assets or their embedded manifests.

## 3. Field registration

Add a unique `slug` and English `name` and `summary` to `catalog.json`'s `fields` array:

```json
{
  "slug": "stellar-physics",
  "name": {
    "en": "Stellar physics"
  },
  "summary": {
    "en": "Explore stellar structure and oscillations through papers, explanations, and reproduction materials."
  }
}
```

Field titles, descriptions, breadcrumbs, and paper-card field labels use these values. Each paper's `field` must match a registered field slug. Supply the English strings, and use `["en"]` for both the catalog's top-level `languages` and each paper's `languages`.

## 4. Paper metadata and article files

A complete example entry in the `papers` array is shown below. Page counts, reading times, names, and scope statements are illustrative; replace them with values established for the actual paper and guides. Register the example figure before using its ID.

```json
{
  "slug": "star-modes",
  "field": "stellar-physics",
  "archive_slug": "compact-star-modes",
  "title": "Example paper title",
  "short_title": "Star modes",
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
    "en": "The paper's question and the scope of its results."
  },
  "page_counts": {
    "main": 12,
    "supplement": 6
  },
  "audience_descriptions": {
    "general": {"en": "Understand the question through accessible examples."},
    "student": {"en": "Connect foundational equations to the model and calculations."},
    "expert": {"en": "Examine definitions, assumptions, and tests in detail."}
  },
  "reading_times": {
    "general": "15–25",
    "student": "25–40",
    "expert": "35–50"
  },
  "scope": {
    "en": [
      "Research themes covered at every reading level.",
      "Conditions applying to the diagrams and calculations."
    ]
  },
  "hero_figure": "star-modes-student-overview",
  "interactive_return": false
}
```

`slug` is the site's short paper name; `archive_slug` names the original-material directory. `source_path` is relative to the repository root, while PDF paths are relative to `docs/`. Give each paper distinct release names and keep its registered version aligned with its original files and distribution records.

| Metadata | Use and behavior when optional values are omitted |
| --- | --- |
| `title`, `short_title` | Paper headings, breadcrumbs, and a single-paper collection summary. An omitted short title falls back to `title`. |
| `version` | Article headers, download labels, and provenance statements. Required and matched to the original version. |
| `page_counts.main`, `.supplement` | Page counts in PDF buttons. An omitted count is not displayed. |
| `audience_descriptions` | Reading-level cards and end navigation. A missing level or language uses a neutral default. |
| `reading_times` | Approximate reading times. If absent, the label mentions the opening TL;DR without a time estimate. |
| `scope.en` | Scope paragraphs on the paper landing page. Supply an array of strings; if absent, a neutral pointer to the original paper is used. |
| `hero_figure` | Illustration on paper listings. If absent, no illustration is inserted; an unregistered ID raises an error. |
| `interactive_return` | Explicitly enables the two-group ideal-return interactive explanation. The default is false; it is currently enabled only for CAT. |

Collection summaries use the selected paper's title and version for one paper, or the paper count for multiple papers. A newly registered paper does not inherit CAT's title, version, page counts, figures, or reading times. The ideal-return calculation is a particular mathematical model; enable it only when it applies to the paper being explained.

One current template limit requires a separate check: article headers still use the fixed label `Research preprint`, and catalog footers mention a preprint and the author's and AI's contributions. These strings are not inferred from paper metadata. Before publishing a paper with different review status or contribution history, update those template statements to accurately describe each paper and the collection. The presence of a catalog entry does not establish AI involvement or peer-review status.

For `content_prefix: "star-modes-"`, supply exactly these three fragments:

- `content/star-modes-general-en.html`
- `content/star-modes-student-en.html`
- `content/star-modes-expert-en.html`

CAT currently uses an empty prefix. Give other papers distinct prefixes; reusing the empty prefix would load CAT's fragments. The three guides cover the same research topics, conditions, conclusions, and sources, with explanatory depth adapted to the reader.

## 5. Article fragment format

A fragment contains one `article`, not a complete HTML document:

```html
<article lang="en">
  <header class="article-header">
    <h1>Understanding the example model</h1>
    <p class="lead">Connect the physical question to its mathematical model.</p>
  </header>
  <aside class="tldr" id="star-modes-student-tldr">
    <h2>TL;DR</h2>
    <p>State the question, result, assumptions, and remaining limitations.</p>
  </aside>
  <section id="star-modes-student-model">
    <h2 id="star-modes-student-model-heading">Understand the model</h2>
    <p>Develop one idea at a time in short, connected paragraphs.</p>
    <div data-figure="star-modes-student-overview"></div>
    <p><a href="{{PAPER_PDF}}#page=2">The relevant page of the paper</a></p>
    <p><a href="{{SOURCE_ROOT}}/main.tex">Original source</a></p>
  </section>
</article>
```

The builder moves the TL;DR to the start of the article, places the `h1` in the common header, and builds the contents list from `h2` headings. The TL;DR also requires an `h2`. Use unique and stable IDs for sections and headings so that coverage records and links remain meaningful.

The replacement tokens are `{{PAPER_PDF}}`, `{{SUPP_PDF}}`, and `{{SOURCE_ROOT}}`. The first two become local PDF links. The last becomes a GitHub link to the original files at the paper's configured Release tag. Check page numbers and source filenames against that exact version.

Use `\(...\)` for inline mathematics and `<div class="equation">\[...\]</div>` for displayed equations. Explain symbols, units, and validity conditions, and connect the expression to the original paper. Escape `<` and `>` as HTML entities where required. A KaTeX error stops the build.

Distinguish physical assumptions, conditional results, proposed experiments, observations, and open questions at every reading level. Record the source-to-section mapping in the version's `reading-guides/COVERAGE.md`; record content checks and corrections in its `reading-guides/SCIENTIFIC_QA.md`.

## 6. English SVG figures

Define a named function in `figures.py` that accepts `lang` and returns `(inner_svg_markup, height)`. Existing helpers such as `text`, `rect`, and `arrow` can be reused; the common SVG width is 880.

Register the HTML figure ID in `MAP` and its English title and description in `CAPTIONS`, keyed by the **function name**:

```python
MAP['star-modes-student-overview'] = star_modes_overview
CAPTIONS['star_modes_overview'] = {
    'en': {
        'title': 'Example figure title',
        'description': 'Explain the conditions and meaning in English.'
    }
}
```

The dictionary format is supported for new figures. The existing four-element caption format remains supported, with positions 1 and 3 providing the English title and description. No additional language version is required.

`figure()` adds a `figure-` ID, an accessible SVG title, and a caption. Do not insert the same figure ID twice in a page or use a section ID that collides with the generated ID. Pair colors with labels or line styles. For calculated plots, preserve traceable inputs and identify axes, units, parameters, errors, and conditions. Distinguish diagrams, calculations, and observations; check legibility and scrolling on narrow screens.

## 7. PDFs and version correspondence

Place each PDF at the `docs/` path registered in the catalog, preserving the supplied original bytes. Record its independently obtained SHA-256 and extend `tools/verify_site.py`'s PDF identity checks. Its current expected-hash table contains the two CAT Version 4 PDFs; adding a catalog entry does not automatically add a new PDF identity check. Retain existing checks when adding others.

Download labels read version and optional page counts from the catalog. Keep original files, verification records, and Release tags aligned with that version. Adding `source_path` or `archive_slug` does not generate research READMEs, provenance, coverage, QA, or publication manifests; those records must be maintained separately.

## 8. Build and verification

From the repository root, use Node.js and Python 3 with the pinned dependencies. A dedicated Python virtual environment is described in [the publication guide](../ADDING_PAPERS.md#91-generate-the-site-and-run-structural-checks).

```sh
npm ci
python3 -m pip install -r site-src/requirements.txt
python3 tools/build_site.py
python3 tools/verify_site.py
```

Check the exit codes and `verification.json`'s `error_count`. The verifier checks local links and anchors, original-source paths, configured English articles, IDs, TL;DR structure, equations and figures, registered PDF hashes, canonical URLs, hreflang links, and sitemap scope. It does not establish scientific correctness or readability; compare each guide with its original paper and use its version-specific QA record.

For a local visual review:

```sh
python3 -m http.server 8000 --directory docs
```

Review the shared entry, English index, field and paper pages, and all three guides per paper on desktop and narrow screens. Check navigation, long equations, tables and figures, PDF links, and original sources.

Removing or renaming a catalog entry does not automatically delete old generated HTML. Review obsolete pages and retained-version links explicitly. The build also leaves ownership files under manual control; a removed IndexNow key file stays removed.

Local generation does not push Git changes, configure Pages, create Releases, or submit search notifications. Follow [ADDING_PAPERS.md](../ADDING_PAPERS.md) for publication, and record completion only after the corresponding remote operations and live checks succeed.
