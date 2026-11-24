# Frozen CAT v4 release reconstruction

This directory reconstructs the five existing CAT Version 4 release assets
without adding the bundled third-party runtimes to Git. Every input and every
final asset must match the original byte count and SHA256 hash before publication.
The 742 original scientific-package files remain unchanged.

The workflow is specific to `gawakkyu0603-bit/physics`, Release `cat-v4.0.0`.
It is manually dispatched, uses the standard `ubuntu-24.04` runner and its system
Python, and attaches assets only to an **already published Release with an existing
tag**. It does not create a Release, create or move a remote tag, replace an existing
asset, or change research files.

## Inputs and provenance

| Source | Original files | How identity is checked |
| --- | ---: | --- |
| `quantum-gravity/correlation-actualization-theory/v4/paper/` | 709 | Every path, size and SHA256 in the frozen publication manifest |
| Official upstream distributions | 31 | Explicit HTTPS URL, size and SHA256 in `inputs.json` |
| Original `distributions.json` files | 2 | Exact original bytes under `embedded/CAT-review/evidence/` |
| Original publication wrapper | 15 | Exact bytes under `embedded/`; its manifest is separately pinned |

The 31 upstream paths comprise 26 Python wheels, the CPython 3.14.7 Windows
embedded archive, Lean 3.51.1 for Linux and Windows, and the pinned mathlib3 source
and compiled cache. Five universal wheels occur in both platform directories, so
only 26 distinct downloads are needed: **287,086,434 bytes** in total.

All upstream distributions were downloaded from the following official sources
on 25 November 2026 JST, and their SHA256 hashes matched the supplied v4 package:

- Python packages: exact `files.pythonhosted.org` URLs retained in the original
  platform `distributions.json` files.
- CPython: <https://www.python.org/ftp/python/3.14.7/python-3.14.7-embed-amd64.zip>.
- Lean: <https://github.com/leanprover-community/lean/releases/tag/v3.51.1>.
- mathlib3 source: commit `65a1391a0106c9204fe45bc73a039f056558cb83`, using the
  corresponding official GitHub codeload archive.
- mathlib3 cache:
  <https://oleanstorage.azureedge.net/mathlib/65a1391a0106c9204fe45bc73a039f056558cb83.tar.xz>,
  following the `scripts/fetch_olean_cache.sh` URL in that source revision.

`inputs.json` records each complete download URL and each expected hash. Downloads
are treated as opaque distribution files; their code is not installed or executed.

## Frozen notices

The files under `embedded/` are the **frozen bundle-reproducibility snapshot**.
They preserve the original complete bundle's notices, licenses, citations and
manifest. They are not replacements for the current repository documentation.
Their relative links use `CAT-review/`, the directory name inside the complete ZIP.
Current repository documents use `paper/` and include the canonical repository
and tag URLs added later. No original research file is modified by either wrapper.

## Exact output

| Asset | Bytes | SHA256 |
| --- | ---: | --- |
| `CAT_v4_full_publication_bundle.zip` | 301,080,385 | `1c4f5ce9f33a531d4c07842a5a64dbeb080d7dea0a5a6b5433e873dbc887e7e7` |
| `CAT_v4_main.pdf` | 455,720 | `5b3539369c18b900a207c1bf8e55e3261a7e9599b6cd8be8181f7c814c68fc7a` |
| `CAT_v4_supplement.pdf` | 378,255 | `96c59915ad3bdafbad4da6b79bb9974f3ba7a644544205070691383fa16b46a8` |
| `CAT_v4_article_source.tar.gz` | 48,663 | `252413fa68fe1b52b12756f91ab07022a784148f61a5b1e16d95a09c9558391c` |
| `SHA256SUMS` | 366 | `055ad20af4cf0d7cf16a1a4602d6b4f1da291ee098b5cfab8bb5278ef75f22c2` |

The ZIP has 757 sorted entries, no directory entries, DEFLATE level 6, timestamps
`2026-11-25 00:00:00`, Unix creator system and regular-file mode `100644`.
The supplied article source archive and PDFs are copied without re-encoding.

Exact reconstruction was validated with both:

- CPython 3.12.14 and zlib 1.3.2.
- CPython 3.13.5 and zlib 1.3.1.

A further end-to-end check used only the 709 Git files, newly downloaded official
distributions and embedded snapshot. All five final hashes matched. The workflow
prints its actual Python/zlib versions and requires the same five final hashes.
If a future compression runtime changes the ZIP bytes, the build fails before
uploading; no approximate reconstruction is accepted. See `validation.json`.

## Local reconstruction

From the repository root, with Python 3.12 or later:

```bash
python3 tools/release_cat_v4/build_release.py \
  --download \
  --cache /tmp/cat-v4-upstream \
  --output /tmp/cat-v4-assets
```

This command builds and verifies files only. It has no GitHub authentication or
publication operation. It downloads about 287 MB and creates about 302 MB of
release assets. Space is also needed for the temporary ZIP while it is built.

For an offline identity check against all 742 extracted original files:

```bash
python3 tools/release_cat_v4/build_release.py \
  --local-full-root /path/to/extracted/CAT-review \
  --output /tmp/cat-v4-assets
```

## Manual Release attachment workflow

1. Create the intended `cat-v4.0.0` tag and publish its Release through the normal
   repository interface. The tag must contain the unchanged 709 original Git files.
2. Open **Actions → Assemble and attach frozen CAT v4 assets → Run workflow**.
3. Select the branch containing this reviewed recipe. The workflow checks out its
   exact triggering commit, fetches the existing tag, and verifies all 709 original
   files at that tag before assembling the distribution.
4. The builder checks all 757 ZIP members and all five final asset hashes.
5. The publisher verifies that the remote tag still resolves to the checked commit.
   It checks existing asset hashes and uploads only missing assets with
   `gh release upload`, without `--clobber`. A different existing asset causes a
   failure. After upload, all five remote asset hashes and the tag are checked again.

For assets that expose GitHub's SHA256 `digest`, the publisher verifies that server
digest. If the digest is absent, it downloads the existing asset and verifies its
bytes. A failed or partially completed attachment can be rerun: already identical
assets are retained, while any conflict stops the run.

The workflow requests only `contents: write`, uses the built-in `GITHUB_TOKEN`
through `GH_TOKEN`, and needs no personal access token or browser credentials.
It uses no extra checkout/setup action and no persistent Actions artifact/cache
storage. According to [GitHub's billing documentation](https://docs.github.com/en/actions/concepts/billing-and-usage),
standard GitHub-hosted runners in public repositories are free. No larger runner
or paid storage feature is configured here.
