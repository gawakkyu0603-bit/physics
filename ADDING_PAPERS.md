# Adding and publishing research papers

[Research index](README.md) · [Publication policy](docs/PUBLICATION_SCOPE.md) · [Catalog and generator reference](site-src/README.md)

This guide explains how to add research to this repository and publish its latest manuscript and three English reading guides. GitHub stores identifiable research versions; GitHub Pages presents only the latest registered version of each paper. Public descriptions focus on the research, available materials, and practical use.

## 1. Prepare the research materials

Organize supplied manuscripts, sources, data, and code as `field/paper/version/paper/`. For example:

| Location | Contents |
| --- | --- |
| `stellar-physics/README.md` | A short field introduction and paper index. |
| `stellar-physics/compact-star-modes/README.md` | The research question, scope, current materials, citation, and reading links. |
| `stellar-physics/compact-star-modes/v1/README.md` | Instructions for this manuscript and its reproduction resources. |
| `stellar-physics/compact-star-modes/v1/paper/` | Supplied original files. |

These names describe a fictional example. Do not copy CAT's scientific statements, file counts, authorship, contribution history, or publication status into another paper.

Keep supplied research files identifiable and preserve fixed tags and published assets. Use a new directory for a new manuscript version. Public READMEs should describe the current research and resources; they do not need reviewer correspondence, resolved-comment checklists, or a chronology of earlier revisions. Retain scientific assumptions and limitations that readers need to interpret the work. Do not infer peer review, a DOI, or a license from publication on GitHub.

Maintain public documentation in English. Build and publishing commands belong in this guide, rather than the root README. Each paper retains its own contribution statements, citation metadata, rights notices, and third-party terms.

## 2. Register the field and manuscript

Edit [site-src/catalog.json](site-src/catalog.json). Its top-level `owner`, `repository`, and `public_base_url` identify the publication destination. GitHub Pages serves `docs/` on `main` at `https://gawakkyu0603-bit.github.io/physics/`. Keep `languages` set to `["en"]` and `sitemap_filename` set to the configured sitemap filename, `sitemap-pages.xml`.

A field needs a unique slug and English name and summary:

```json
{
  "slug": "stellar-physics",
  "name": {"en": "Stellar physics"},
  "summary": {"en": "Research on stellar structure and oscillations."}
}
```

A paper can have a main manuscript without a supplement or a GitHub Release:

```json
{
  "field": "stellar-physics",
  "slug": "star-modes",
  "title": "Example stellar oscillations paper",
  "author": "Author name",
  "version": "1",
  "summary": {"en": "The research question and the actual scope of the results."},
  "source_path": "stellar-physics/compact-star-modes/v1/paper",
  "content_prefix": "star-modes-v1-",
  "languages": ["en"],
  "audiences": ["general", "student", "expert"],
  "documents": [
    {
      "id": "main",
      "label": "Paper PDF",
      "path": "downloads/star-modes-v1-main.pdf",
      "source_path": "stellar-physics/compact-star-modes/v1/paper/main.pdf"
    }
  ]
}
```

The paper's `source_path` names its original-source directory. A document's `source_path` names the particular original file; both are relative to the repository root. A document's `path` is relative to `docs/`. The builder copies declared source files to their published paths without changing their bytes. A document with no source path must already exist at its published path.

`documents` is an optional list. A supplement, dataset, code archive, or other downloadable file is included only when explicitly registered. Neither a supplement nor a PDF is required by the generator. Add a document with `id: "supplement"` only if that resource exists. Labels and optional `page_count` values belong to the individual document; omit page counts when they do not apply.

For independent identity checks, supply a document's actual 64-character `sha256`, its original `source_path`, or both. The verifier reports whether these independent comparisons were performed. A hash merely computed from a served file during verification is an inventory value, not an independent expected hash. Obtain an expected hash from the confirmed original, for example:

```sh
sha256sum stellar-physics/compact-star-modes/v1/paper/main.pdf
```

Optional metadata includes `subtitle`, `date`, `short_title`, `page_counts` for legacy entries, `audience_descriptions`, `reading_times`, `scope`, `hero_figure`, `status_label`, `publication_note`, and `downloads_intro`. See [the catalog reference](site-src/README.md#catalog-and-resources) for their behavior. Use only accurate paper-specific values. A missing publication-status or contribution statement does not imply that the paper is a preprint or that AI was involved.

A `release` tag is optional. Source links use an explicit `source_ref` when provided, otherwise the release tag if configured, otherwise `main`. Use an existing immutable tag or exact commit for archival citations. Do not configure a Release link before that Release exists.

## 3. Keep only the latest manuscript on Pages

The catalog may retain several entries for a paper, identified by the same `field` and `slug`. Use distinct version directories, source fragments, and download paths for each entry. Update the current-paper README and research-index links when introducing a new manuscript. The shared catalog loader selects one latest entry before generating pages, downloads, or the sitemap.

Numeric dotted versions are compared numerically: `10` is later than `2`, and `2.10` is later than `2.9`. Equivalent ranks such as `4` and `4.0` are ambiguous and are rejected. If a series uses nonnumeric labels, give every entry in that series a distinct integer `version_order`; a larger order is newer. Do not use a guessed lexicographic order for names such as `draft-final`.

Pages URLs stay stable, for example `en/stellar-physics/star-modes/index.html`, and display the selected latest manuscript. Root and field pages provide compact research indexes. Paper-specific figures, download descriptions, and the three reading-level cards belong on the paper's landing page.

[site-src/generated-files.json](site-src/generated-files.json) records the generated pages, registered downloads, and sitemap, with their hashes. On a later build, an obsolete recorded output is removed only when its bytes still match that record. If an obsolete output has been changed outside the build, generation stops before publishing any replacement files and preserves the old output manifest. Untracked files and ownership-verification files remain outside this cleanup. Resolve reported stale-file conflicts before publishing; do not erase the output manifest to bypass them. Earlier research directories, fixed tags, and Release assets remain on GitHub.

## 4. Write three complete English introductions

With `content_prefix: "star-modes-v1-"`, provide:

- `site-src/content/star-modes-v1-general-en.html`
- `site-src/content/star-modes-v1-student-en.html`
- `site-src/content/star-modes-v1-expert-en.html`

Give different papers and versions distinct prefixes. Every introduction begins with a TL;DR and explains the complete paper and any supplement, including definitions, assumptions, results, proposed tests, negative results, and open questions. Adjust the teaching depth for the reader while preserving the meaning and scope of the research.

| Audience | Treatment |
| --- | --- |
| General readers | Accessible scientific prose, concrete examples, clear definitions, and diagrams that explain the mechanism and its limits. Explain any required equation in words. |
| STEM students and graduates | Background, intermediate mathematical steps, worked examples, units, and connections to familiar physics. |
| Specialists | Definitions, conditions, derivations, quantitative comparisons, and links to the exact manuscript and source material. |

Use sufficient detail to bridge the reader's background to the paper's arguments. Do not impose an arbitrary word limit or substitute a topic list for an explanation. Prepare a source-to-guide map under the version's `reading-guides/COVERAGE.md` and link it from [the coverage index](site-src/COVERAGE.md). Map each substantive main-paper and supplement topic to stable section IDs in all three guides. Keep this as a current content map rather than a review-response history.

An article fragment contains one `article`:

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
    <h2>Understand the model</h2>
    <p>Develop the argument and identify the conditions under which it holds.</p>
    <p><a href="{{PAPER_PDF}}#page=2">Relevant page of the paper</a></p>
  </section>
</article>
```

The builder puts the TL;DR first, places the `h1` in the page header, and creates a contents list from `h2` headings. IDs must be unique within a page. Use `\(...\)` for inline mathematics and `<div class="equation">\[...\]</div>` for display equations. Escape HTML-sensitive characters where needed. KaTeX errors stop generation.

`{{PAPER_PDF}}` and `{{SUPP_PDF}}` refer to registered `main` and `supplement` documents. `{{DOCUMENT:data}}` refers to the document with ID `data`. `{{SOURCE_ROOT}}` requires a configured source directory. If a resource is absent, remove its reference from the article; the builder reports an explicit error for an unresolved resource token. Do not add a fictitious supplement to satisfy a template.

## 5. Prepare figures and other assets

Use diagrams, quantitative plots, and tables where they help readers follow the argument. Show units, parameters, assumptions, and source locations for calculated values. Distinguish schematics, model calculations, and observations. Pair color with labels or line styles, and check narrow-screen readability.

Define SVG functions in [site-src/figures.py](site-src/figures.py). A function receives `lang` and returns `(inner_svg_markup, height)`; the common width is 880. Register the figure ID and the caption under the function name:

```python
MAP['star-modes-student-overview'] = star_modes_overview
CAPTIONS['star_modes_overview'] = {
    'en': {
        'title': 'Example figure title',
        'description': 'Explain the conditions, quantities, and interpretation.'
    }
}
```

Insert `<div data-figure="star-modes-student-overview"></div>` in the article. The generator adds accessible titles and captions. Do not reuse the same figure ID twice on a page. Legacy four-element caption tuples remain supported for existing figures; the English values are the second and fourth elements.

`hero_figure` is optional and belongs on the paper landing page. `interactive_return` enables a particular ideal-return calculation and defaults to false; enable it only for a paper to which that model applies. Maintain shared CSS, JavaScript, fonts, and images under `docs/assets/` separately from the generated-page cleanup.

## 6. Build and verify

Run commands from the repository root. Install the locked Node dependencies and Python dependencies, preferably in a dedicated environment:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r site-src/requirements.txt
npm ci
python3 tools/build_site.py
python3 tools/verify_site.py
python3 -m unittest discover -s tests -p 'test_site_publication.py'
```

The equivalent build and verification npm scripts are `npm run build` and `npm run verify`. Both Python entry points also accept `--root PATH` for an isolated repository fixture.

Require successful exits and `error_count: 0`. Checks cover the selected latest papers, expected HTML pages, links and anchors, opening TL;DRs, mathematics, figure labels, canonical and hreflang URLs, the configured sitemap, and declared document identity comparisons. The regression tests cover publication behavior across different papers and versions; they do not independently validate the scientific claims.

Review the generated site locally:

```sh
python3 -m http.server 8000 --directory docs
```

Inspect the shared entry, English index, field pages, paper landings, and all three guides on desktop and narrow screens. Confirm that collection pages remain general, paper-specific material is on the appropriate landing, and only the latest manuscript's resources are served. Compare text, equations, figures, and source links against the actual paper. Structural checks do not establish scientific correctness or readability.

Google and Bing ownership-verification files inside `docs/` are maintained separately. Preserve their exact supplied bytes. The builder does not recreate a removed IndexNow key or send search notifications.

## 7. Publish the materials

Review the actual diff before committing. Include the intended research files, catalog and article sources, updated public documentation, generated `docs/` files, build records, and output manifest. Avoid committing temporary execution environments or review correspondence as public explanatory documents. Use a branch and pull request when appropriate to the repository's workflow, and publish the agreed changes to `main`.

If a version directory has a `PUBLICATION_MANIFEST.json`, update its size and SHA-256 records to match that directory's current public files, excluding the manifest itself. Preserve independent source hashes and fixed manifests inside existing Release assets. Do not rebuild a fixed distribution merely because website descriptions changed.

A GitHub Release is optional. When one is appropriate, tag the intended publication commit with a paper-specific name, prepare only the assets that actually exist, and describe their current contents and use. A paper without a supplement does not need a supplement asset. For example:

```sh
git tag -a star-modes-v1.0.0 -m 'Publish the stellar oscillations paper'
git push origin star-modes-v1.0.0
gh release create star-modes-v1.0.0 --verify-tag \
  --title 'Stellar oscillations paper' \
  --notes-file /path/to/prepared-release-description.md \
  /path/to/star-modes-v1-main.pdf /path/to/SHA256SUMS
```

Use actual filenames and a prepared description of the paper, resources, and usage. Existing tags and assets remain fixed. GitHub's automatic source ZIP and tarball contain the repository tree at the tag; they do not add runtimes omitted from Git. A paper-specific complete distribution should state its own contents.

Confirm that the `main` / `docs` Pages deployment succeeds and that the public URLs match the checked files. Publication is complete only after the repository and required live resources are available.

## 8. Sitemap and search registration

The current sitemap is [sitemap-pages.xml](https://gawakkyu0603-bit.github.io/physics/sitemap-pages.xml), generated from the canonical HTML pages of the latest registered manuscripts. It excludes ownership files, older manuscript outputs, and download files. Downloadable manuscripts remain discoverable through their paper pages. The former `sitemap.xml` filename is retired.

After deploying a changed sitemap filename, use the new absolute URL in the site's Google Search Console sitemap form. Search Console receives a URL; the XML file itself is hosted by GitHub Pages. The current change replaces the previously failing filename at the author's request. Do not describe the Google-side error as resolved until Search Console reports successful retrieval. See Google's [sitemap guidance](https://developers.google.com/search/docs/crawling-indexing/sitemaps/build-sitemap) and [Sitemaps report help](https://support.google.com/webmasters/answer/7451001).

Service-issued ownership files go under `docs/`, so `docs/BingSiteAuth.xml` is served as `https://gawakkyu0603-bit.github.io/physics/BingSiteAuth.xml`. Use the exact filename and bytes issued for the correct site. Existing Google and Bing ownership registrations do not need to be repeated for an ordinary content update. No periodic monitoring or automatic resubmission is part of this publication workflow. The separate IndexNow script is manual and requires its configured verification file; it is not run by a site build.
