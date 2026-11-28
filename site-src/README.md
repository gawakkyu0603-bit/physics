# Site source reference

[Research index](../README.md) · [Publication policy](../docs/PUBLICATION_SCOPE.md) · [Adding and publishing papers](../ADDING_PAPERS.md)

The reading site is a general physics research index with a dedicated landing page and three English guides for each paper. The catalog selects the latest registered version of each paper. The repository retains current research sources only, and Pages serves that selection at stable URLs.

## Files and responsibilities

| File or directory | Purpose |
| --- | --- |
| [catalog.json](catalog.json) | Fields, manuscripts, optional resources, publication metadata, and the sitemap filename. |
| `content/` | Three English article fragments per registered manuscript. |
| [figures.py](figures.py) | Generic SVG loader; named SVGs and caption sidecars in `figures/`. |
| [render-math.cjs](render-math.cjs) | KaTeX rendering into HTML and MathML. |
| [COVERAGE.md](COVERAGE.md) | Index of current source-to-guide maps. |
| [../tools/site_catalog.py](../tools/site_catalog.py) | Shared catalog validation, version selection, document normalization, and expected-page paths. |
| [../tools/build_site.py](../tools/build_site.py) | Page generation, declared-document publication, sitemap, and obsolete-output cleanup. |
| [../tools/verify_site.py](../tools/verify_site.py) | Structural, link, document-identity, metadata, and sitemap checks. |
| [generated-files.json](generated-files.json) | Managed Pages output paths, roles, and hashes used by subsequent builds. |
| [build-stats.json](build-stats.json) / [verification.json](verification.json) | Generated build and mechanical-verification results. |
| `../docs/assets/` | Shared styling, scripts, fonts, and images maintained outside page generation. |

[ADDING_PAPERS.md](../ADDING_PAPERS.md) contains the complete publication procedure. The reference below describes the implemented formats and boundaries.

## Catalog and resources

The top-level catalog identifies `owner`, `repository`, `public_base_url`, `languages`, `fields`, `papers`, and `sitemap_filename`. The public base URL ends in `/`. The current language is `["en"]`; the current sitemap filename is `sitemap.xml`.

A field has a unique `slug` and English `name` and `summary`. A manuscript entry requires a registered `field`, a site `slug`, its `title`, and a `version`. The same field and slug identify one paper; keep its entry and paths fixed when replacing the current manuscript. The archive directory can have a longer name and is specified by the source paths.

| Paper metadata | Behavior |
| --- | --- |
| `version`, optional `version_order` | Select the latest manuscript per field and slug. Numeric dotted versions use numeric comparison. If a series uses nonnumeric labels, supply a distinct integer order for every entry. Equal ranks are rejected. |
| `author`, `date`, `subtitle`, `summary.en`, `short_title` | Paper-specific display text. Omitted values do not copy another paper's metadata. |
| `content_prefix` | Prefix of this manuscript's three source-fragment filenames. Use a distinct prefix for each paper, retaining it when updating that paper. |
| `languages`, `audiences` | English and the three reading levels: `general`, `student`, `expert`. |
| `source_path` | Optional original-source directory, relative to the repository root. Required only when an article uses `{{SOURCE_ROOT}}`. |
| `source_ref`, `release` | Source links use `source_ref`, otherwise the optional release tag, otherwise `main`. A release link appears only when configured. |
| `documents` | Optional list of actual downloadable resources. No main PDF, supplement, source archive, or Release is assumed. |
| `audience_descriptions` | Optional English descriptions for each reading level; neutral defaults apply where absent. |
| `reading_times` | Optional reading-time estimates by audience. No estimate is displayed when absent. |
| `scope.en` | Optional array of paragraphs on the paper landing page. |
| `hero_figure` | Optional registered figure on the paper landing page. An unknown figure ID is an error. |
| `status_label` | Optional internal metadata; not rendered by shared templates. |
| `publication_note` | Optional internal metadata; not rendered by shared templates. |
| `downloads_intro` | Optional introduction to that paper's available downloads. |

The optional text fields accept English strings or `en` dictionaries. Only `downloads_intro` is rendered by the shared presentation; status and publication notes are not automatically displayed.

Each document is declared independently:

```json
{
  "id": "main",
  "label": "Paper PDF",
  "path": "downloads/star-modes-v1-main.pdf",
  "source_path": "stellar-physics/compact-star-modes/v1/paper/main.pdf"
}
```

`id`, `label`, and `path` are required for a declared document. `path` is relative to `docs/`; optional `source_path` is relative to the repository root. Optional `sha256` supplies an independently confirmed expected hash, and optional `page_count` adds a count to the label. A dataset or archive need not have a page count or a `.pdf` extension.

With `source_path`, the builder copies the original bytes to the declared publication path and checks an expected hash when provided. Without it, the published file must already exist. The verifier checks every specified source or expected hash. If neither is configured, it checks existence and records the digest while reporting that no independent identity comparison was available.

Legacy `main_pdf`, `supplement_pdf`, and `page_counts` entries remain accepted and are normalized into documents. New entries should use `documents`. Omitting the supplement is valid; an empty or absent document list is also valid when the articles do not reference missing downloads.

## Latest-version publication and cleanup

`load_catalog(root)` is shared by generation and verification. Its current `papers` list contains one latest manuscript per field and slug; `all_papers` retains the registered entries for catalog reasoning. The site uses the selected list for indexes, paper pages, reading guides, downloads, and sitemap URLs.

Numeric version comparison handles `2 < 10` and `2.9 < 2.10`. `4` and `4.0` have the same rank and cannot both serve as distinct candidates. Nonnumeric versions require explicit ordering for the entire series. A directory elsewhere in Git is not automatically published merely because it exists.

The builder records managed paths in `generated-files.json`:

```json
{
  "schema_version": 1,
  "files": [
    {"path": "en/index.html", "role": "page", "sha256": "the actual SHA-256"},
    {"path": "downloads/example.pdf", "role": "document", "sha256": "the actual SHA-256"},
    {"path": "sitemap.xml", "role": "sitemap", "sha256": "the actual SHA-256"}
  ]
}
```

The hash strings above illustrate the record layout; real records contain 64 hexadecimal characters. Subsequent builds remove obsolete managed files only when their current bytes match the prior record. A modified obsolete file stops the build before any public output or prior manifest is replaced; resolve the conflict explicitly. Unknown files and Google or Bing ownership files are preserved. Register only paths intended to be managed by this generator; never point a document output at a source or ownership file.

On the first build without a previous output manifest, unknown historical files are not automatically discovered or erased. Review any extra pages reported by verification. Keep the resulting manifest in Git so later version changes can clean their old generated outputs safely. Original research source directories and any separately fixed citation assets are outside generated-output cleanup; approved manuscript replacement explicitly removes superseded source files.

## Page organization

`docs/index.html` and `docs/en/index.html` are general research entrances. Field pages are compact paper indexes. A paper can appear there as a title, a short research summary, and a link; its figure, detailed scope, reading-level cards, and download descriptions belong on its landing page.

For a paper with field `stellar-physics` and slug `star-modes`, the current landing page is `en/stellar-physics/star-modes/index.html`. The general, student, and expert guides use the corresponding audience name plus `.html`. These URLs do not acquire version suffixes; their current content follows the latest selected manuscript.

Every generated HTML page has a canonical URL and English language metadata. The shared entry and English index form the `en`/`x-default` alternate set. The configured XML sitemap contains current canonical HTML pages only. PDFs and other resources are reached through their paper pages and are not sitemap entries. Ownership files and historical outputs are not listed.

## Article fragments and resource tokens

Active papers must use distinct content prefixes; duplicate prefixes, including two empty prefixes, are rejected before generation. The prefix `star-modes-v1-` selects:

- `content/star-modes-v1-general-en.html`
- `content/star-modes-v1-student-en.html`
- `content/star-modes-v1-expert-en.html`

Each fragment contains one `<article lang="en">`, a header with `h1`, an opening `<aside class="tldr">` with an `h2`, and substantive sections. The builder puts the TL;DR first and creates navigation from `h2` headings. IDs must be unique within the page.

| Token | Required configuration |
| --- | --- |
| `{{PAPER_PDF}}` | Document with ID `main`. |
| `{{SUPP_PDF}}` | Document with ID `supplement`. |
| `{{DOCUMENT:data}}` | Document with ID `data`; other IDs use the same syntax. |
| `{{SOURCE_ROOT}}` | Paper `source_path`, with the selected source ref. |

Missing resource references produce a concrete build error. Do not manufacture an absent supplement or leave an unresolved link in the rendered page. Check source filenames and PDF page anchors against the selected manuscript.

Use `\(...\)` for inline mathematics and `<div class="equation">\[...\]</div>` for display equations. Explain notation and conditions, and escape HTML-sensitive characters where needed. Rendering errors stop the build. [ADDING_PAPERS.md](../ADDING_PAPERS.md#5-prepare-figures-and-other-assets) describes SVG registration and accessibility.

## Commands and verification boundaries

From the repository root, with dependencies installed:

```sh
python3 tools/build_site.py
python3 tools/verify_site.py
python3 -m unittest discover -s tests -p 'test_site_publication.py'
```

The build and verification commands accept `--root PATH` for an isolated checkout. They update their generated outputs and reports. Neither command pushes to GitHub or sends search notifications.

The structural verifier checks configured pages, current manuscript selection, local links and anchors, source targets, language and canonical metadata, TL;DR structure, mathematics, figure labels, sitemap coverage, and declared document identity. The regression tests use temporary fixtures for different paper/resource/version configurations. Scientific accuracy still requires comparison with the actual manuscript; mechanical checks are not a review of the research.

Ownership-verification files are maintained manually under `docs/`. Ordinary builds preserve them and do not restore the removed IndexNow key. [indexnow.json](indexnow.json) is configuration for the separate manual notification script, which reads the catalog's sitemap filename and requires a valid key before sending anything. Search registration instructions are in [ADDING_PAPERS.md](../ADDING_PAPERS.md#8-sitemap-and-search-registration).

## Figure sources

Each named SVG is stored in `site-src/figures/<id>.svg` with a JSON sidecar containing `title` and `description`. The generic `figures.py` renderer embeds these with accessible captions. Set `hero_figure` or place a `data-figure` element in a guide. Reuse a scientific figure only when its labels and assumptions fit the new work. Public templates omit automatic version badges and review metadata. The internal latest-version ordering is unchanged.

## Related papers and approved archives

An optional `series` slug and positive integer `series_order` identify distinct works in a scientific reading sequence, not revisions. The selected manuscripts retain catalogue group placement and are sorted within each series; the landing pages and reading guides link other members. Duplicate active sequence positions are rejected. An approved archive manifest may activate a new catalogue entry only after its ZIP and per-file identities match. An optional `web_figures` list converts original PDF figures with `pdftocairo` into accessible SVGs with unique IDs, retaining original PDF bytes. See [ADDING_PAPERS.md](../ADDING_PAPERS.md) for the workflow.

## Stable current research collection

The current-series manifest pins the three archives. The batch importer replaces existing source directories in place, registers stable PDF paths and converts source figures. Legacy `v1` path names are retained for existing links; the new work uses `materials/`. Publication checks cover sequence, all current source trees, document identity and public presentation. The generic import dispatcher supports ordinary single-paper manifests as well as explicitly approved batches. Batch-specific identity checks run only for that batch.
