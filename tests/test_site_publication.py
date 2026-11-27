"""Publication regressions using isolated, synthetic research collections.

No production docs are rebuilt, original research is read or changed, or network
requests are made. Run: python3 -m unittest discover -s tests -v
"""
from contextlib import redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

REPOSITORY = Path(__file__).resolve().parents[1]
TOOLS = REPOSITORY / "tools"
sys.path.insert(0, str(TOOLS))

from site_catalog import load_catalog  # noqa: E402
import submit_indexnow  # noqa: E402
from verify_site import verify_site  # noqa: E402


class PublicationFixture:
    def __init__(self, root):
        self.root = root
        self.catalog = {
            "owner": "example-research",
            "repository": "collection",
            "public_base_url": "https://example-research.github.io/collection/",
            "languages": ["en"],
            "sitemap_filename": "sitemap-pages.xml",
            "fields": [{
                "slug": "stellar-physics",
                "name": {"en": "Stellar physics"},
                "summary": {"en": "Synthetic publication regression fixtures."},
            }],
            "papers": [],
        }
        self.write("site-src/figures.py", 'def figure(fid, lang):\n    raise ValueError("No generated fixture figure: " + fid)\n')
        self.write("docs/assets/site.css", "/* Fixture asset. */\n")
        self.write("docs/assets/site.js", "// Fixture asset.\n")
        self.write("docs/assets/favicon.svg", '<svg xmlns="http://www.w3.org/2000/svg"/>\n')
        self.write("docs/googleabcdef12.html", "google-site-verification: googleabcdef12.html\n")
        self.write("docs/BingSiteAuth.xml", "<users><user>fixture-ownership-token</user></users>\n")
        self.ownership = {
            name: (root / "docs" / name).read_bytes()
            for name in ["googleabcdef12.html", "BingSiteAuth.xml"]
        }

    def write(self, relative, data):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(data, bytes):
            path.write_bytes(data)
        else:
            path.write_text(data, encoding="utf-8")
        return path

    def save(self):
        self.write("site-src/catalog.json", json.dumps(self.catalog, indent=2) + "\n")

    def paper(self, slug="modes", version="1", field="stellar-physics", documents=True):
        paper = {
            "slug": slug,
            "field": field,
            "archive_slug": slug + "-research",
            "title": f"{slug.title()} research",
            "subtitle": "A synthetic fixture for publication behavior",
            "author": "Fixture Author",
            "version": version,
            "date": "2026-11-26",
            "content_prefix": f"{slug}-v{version}-",
            "audiences": ["general", "student", "expert"],
            "languages": ["en"],
            "summary": {"en": "A distinct paper with its own supplied materials."},
            "documents": [],
        }
        self.catalog["papers"].append(paper)
        if documents:
            self.document(paper, "main", ".pdf", "both")
        self.fragments(paper)
        return paper

    def document(self, paper, identifier, extension, identity="both"):
        filename = identifier + extension
        source = f"{paper['field']}/{paper['archive_slug']}/v{paper['version']}/paper/{filename}"
        published = f"downloads/{paper['slug']}-v{paper['version']}-{filename}"
        data = f"Synthetic original: {paper['slug']} version {paper['version']}, {identifier}\n".encode()
        if extension == ".html":
            data = b"<!doctype html><title>Supplied notes</title><p>Original supporting notes.</p>\n"
        self.write(source, data)
        self.write("docs/" + published, data)
        document = {"id": identifier, "label": identifier.title() + " document", "path": published}
        if identity in {"both", "source"}:
            document["source_path"] = source
        if identity in {"both", "hash"}:
            document["sha256"] = hashlib.sha256(data).hexdigest()
        paper["documents"].append(document)
        return document

    def fragments(self, paper, extra="", with_figure=True):
        main_link = '<p><a href="{{PAPER_PDF}}">Read the supplied main document</a></p>' if any(
            document["id"] == "main" for document in paper["documents"]
        ) else ""
        for audience in paper["audiences"]:
            diagram = f'''<figure class="diagram" id="{audience}-figure"><svg viewBox="0 0 100 30" role="img"><title>Fixture schematic</title>
<text x="2" y="20">Conditional example</text></svg><figcaption>An explanatory schematic.</figcaption></figure>''' if with_figure else ""
            body = f"""<article lang="en">
<header class="article-header"><h1>{paper['title']} — {audience} — version {paper['version']}</h1>
<p class="lead">Background for this synthetic research paper.</p></header>
<aside class="tldr" id="{audience}-tldr"><h2>TL;DR</h2><p>Question, conditional result, and limits.</p></aside>
<section id="{audience}-result"><h2 id="{audience}-result-heading">Result and conditions</h2>
<p>The supplied version is {paper['version']}; this example makes no scientific evidence claim.</p>
{diagram}
{main_link}{extra}
</section></article>
"""
            self.write(f"site-src/content/{paper['content_prefix']}{audience}-en.html", body)

    def build(self):
        self.save()
        return subprocess.run(
            [sys.executable, str(TOOLS / "build_site.py"), "--root", str(self.root)],
            cwd=self.root, text=True, capture_output=True, timeout=30,
        )

    def sitemap_urls(self):
        tree = ET.parse(self.root / "docs" / self.catalog["sitemap_filename"])
        ns = "{http://www.sitemaps.org/schemas/sitemap/0.9}"
        return [node.text for node in tree.findall(ns + "url/" + ns + "loc")]


class PublicationRegressionTests(unittest.TestCase):
    def setUp(self):
        self.directory = TemporaryDirectory(prefix="physics-publication-test-")
        self.addCleanup(self.directory.cleanup)
        self.fixture = PublicationFixture(Path(self.directory.name))

    def build_successfully(self):
        completed = self.fixture.build()
        self.assertEqual(completed.returncode, 0, completed.stdout + completed.stderr)
        return completed

    def verify_successfully(self):
        report = verify_site(self.fixture.root)
        self.assertEqual(report["error_count"], 0, json.dumps(report["errors"], indent=2))
        return report

    def test_single_paper_without_supplement_or_optional_research_metadata(self):
        self.fixture.paper()
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["html_pages"], 7)
        self.assertEqual(report["checks"]["article_pages"], 3)
        urls = self.fixture.sitemap_urls()
        self.assertEqual(len(urls), 7)
        self.assertTrue(all(url.endswith(".html") for url in urls))
        html = (self.fixture.root / "docs/en/stellar-physics/modes/expert.html").read_text()
        for absent in ["Supplement", "Research preprint", "AI’s contributions", "Verification scope", "cat-v4"]:
            self.assertNotIn(absent, html)
        self.assertNotIn("/releases/tag/", html)
        self.assertNotIn("VERIFICATION.md", html)
        self.assertNotIn("README.md", html)

    def test_multiple_distinct_papers_with_arbitrary_documents_and_no_documents(self):
        first = self.fixture.paper("modes")
        self.fixture.document(first, "notes", ".html", "hash")
        self.fixture.fragments(first, '<p><a href="{{DOCUMENT:notes}}">Supporting notes</a></p>')
        self.fixture.catalog["fields"].append({
            "slug": "fluid-dynamics", "name": {"en": "Fluid dynamics"}, "summary": {"en": "Independent work."},
        })
        second = self.fixture.paper("vortices", "3", "fluid-dynamics", documents=False)
        second["status_label"] = "Published article"
        second["publication_note"] = "A distinct publication status supplied for this paper."
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["html_pages"], 12)
        self.assertEqual(report["checks"]["article_pages"], 6)
        self.assertEqual(len(self.fixture.sitemap_urls()), 12)
        self.assertFalse(any("/downloads/" in url for url in self.fixture.sitemap_urls()))
        second_html = (self.fixture.root / "docs/en/fluid-dynamics/vortices/expert.html").read_text()
        self.assertNotIn("Published article", second_html)
        self.assertNotIn("A distinct publication status supplied for this paper.", second_html)
        self.assertNotIn("Current version:", (self.fixture.root / "docs/en/index.html").read_text())
        self.assertNotIn("· Version ", (self.fixture.root / "docs/en/fluid-dynamics/vortices/index.html").read_text())
        self.assertNotIn("modes-v1-main.pdf", second_html)
        self.assertNotIn("/releases/tag/", second_html)
        self.assertNotIn("AI’s contributions", second_html)

    def test_research_series_is_ordered_independently_of_manuscript_versions(self):
        later = self.fixture.paper("follow-up", "1")
        earlier = self.fixture.paper("foundation", "9")
        later.update(series="linked-research", series_order=2)
        earlier.update(series="linked-research", series_order=1)
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["html_pages"], 11)
        for index in ("docs/index.html", "docs/en/index.html", "docs/en/stellar-physics/index.html"):
            page = (self.fixture.root / index).read_text()
            self.assertLess(page.index("Paper 1 — Foundation research"), page.index("Paper 2 — Follow-Up research"))
        first = (self.fixture.root / "docs/en/stellar-physics/foundation/index.html").read_text()
        second = (self.fixture.root / "docs/en/stellar-physics/follow-up/index.html").read_text()
        self.assertIn('../follow-up/index.html', first)
        self.assertIn('../foundation/index.html', second)
        self.assertNotIn("Current version:", first)

    def test_latest_numeric_version_wins_and_previous_download_is_retired(self):
        older = self.fixture.paper("modes", "2")
        self.build_successfully()
        old_document = older["documents"][0]
        old_original = self.fixture.root / old_document["source_path"]
        original_bytes = old_original.read_bytes()
        newer = self.fixture.paper("modes", "10")
        self.fixture.catalog["papers"] = [newer, older]
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["selected_versions"], {"stellar-physics/modes": "10"})
        self.assertEqual(report["checks"]["html_pages"], 7)
        self.assertFalse((self.fixture.root / "docs" / old_document["path"]).exists())
        self.assertTrue((self.fixture.root / "docs" / newer["documents"][0]["path"]).is_file())
        self.assertEqual(old_original.read_bytes(), original_bytes)
        page = (self.fixture.root / "docs/en/stellar-physics/modes/general.html").read_text()
        self.assertIn("version 10", page)
        self.assertNotIn("modes-v2-main.pdf", page)
        self.assertEqual(len(load_catalog(self.fixture.root)["all_papers"]), 2)

        # Explicit ordering must not override the natural order of numeric versions.
        older["version_order"] = 100
        newer["version_order"] = 1
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["selected_versions"], {"stellar-physics/modes": "10"})
        self.assertFalse((self.fixture.root / "docs" / old_document["path"]).exists())
        page = (self.fixture.root / "docs/en/stellar-physics/modes/general.html").read_text()
        self.assertIn("version 10", page)
        self.assertNotIn("modes-v2-main.pdf", page)

    def test_removed_paper_pages_are_cleaned_but_manual_ownership_files_survive(self):
        older = self.fixture.paper("old-modes")
        self.build_successfully()
        old_page = self.fixture.root / "docs/en/stellar-physics/old-modes/expert.html"
        self.assertTrue(old_page.is_file())
        self.fixture.catalog["papers"] = []
        self.fixture.paper("new-modes")
        self.build_successfully()
        self.verify_successfully()
        self.assertFalse(old_page.exists())
        self.assertFalse((self.fixture.root / "docs" / older["documents"][0]["path"]).exists())
        for name, expected in self.fixture.ownership.items():
            self.assertEqual((self.fixture.root / "docs" / name).read_bytes(), expected)
        self.assertFalse((self.fixture.root / "docs/e81508ec01118f8fa87bfd01b38042cf.txt").exists())

    def test_cleanup_refuses_a_manually_changed_retired_download_atomically(self):
        older = self.fixture.paper("modes", "2")
        self.build_successfully()
        manifest = self.fixture.root / "site-src/generated-files.json"
        page = self.fixture.root / "docs/en/stellar-physics/modes/expert.html"
        manifest_before, page_before = manifest.read_bytes(), page.read_bytes()
        retired = self.fixture.root / "docs" / older["documents"][0]["path"]
        manually_changed = retired.read_bytes() + b"Manual addition outside the generated snapshot.\n"
        retired.write_bytes(manually_changed)
        self.fixture.paper("modes", "10")
        completed = self.fixture.build()
        self.assertNotEqual(completed.returncode, 0)
        self.assertEqual(retired.read_bytes(), manually_changed)
        self.assertEqual(manifest.read_bytes(), manifest_before)
        self.assertEqual(page.read_bytes(), page_before)

    def test_readable_guides_may_have_no_figures(self):
        paper = self.fixture.paper()
        self.fixture.fragments(paper, with_figure=False)
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["article_pages"], 3)
        page = (self.fixture.root / "docs/en/stellar-physics/modes/general.html").read_text()
        self.assertNotIn("<figure", page)

    def test_configured_hash_detects_coordinated_source_and_served_file_changes(self):
        paper = self.fixture.paper()
        self.build_successfully()
        self.verify_successfully()
        document = paper["documents"][0]
        for filename in [document["source_path"], "docs/" + document["path"]]:
            self.fixture.write(filename, b"Both copies changed after the independent digest was recorded.\n")
        report = verify_site(self.fixture.root)
        self.assertGreater(report["error_count"], 0)
        self.assertTrue(any("independent SHA-256" in str(error) for error in report["errors"]))

    def test_source_only_identity_detects_a_modified_served_document(self):
        paper = self.fixture.paper(documents=False)
        document = self.fixture.document(paper, "main", ".pdf", "source")
        self.fixture.fragments(paper)
        self.build_successfully()
        self.verify_successfully()
        self.fixture.write("docs/" + document["path"], b"A changed served copy.\n")
        report = verify_site(self.fixture.root)
        self.assertTrue(any("original source bytes" in str(error) for error in report["errors"]))

    def test_document_without_identity_evidence_is_explicitly_unchecked(self):
        paper = self.fixture.paper()
        document = self.fixture.document(paper, "measurements", ".csv", "none")
        self.build_successfully()
        report = self.verify_successfully()
        identity = report["checks"]["document_identity"]["stellar-physics/modes/v1/measurements"]
        self.assertEqual(identity["identity"], "unchecked")
        self.assertEqual(identity["methods"], [])
        self.assertEqual(
            report["checks"]["document_sha256"][document["path"]],
            hashlib.sha256((self.fixture.root / "docs" / document["path"]).read_bytes()).hexdigest(),
        )

    def test_document_cannot_verify_its_identity_against_itself(self):
        paper = self.fixture.paper()
        self.build_successfully()
        document = paper["documents"][0]
        document.pop("sha256")
        document["source_path"] = "docs/" + document["path"]
        self.fixture.save()
        report = verify_site(self.fixture.root)
        self.assertTrue(any("distinct from the served file" in str(error) for error in report["errors"]))

    def test_missing_configured_optional_document_fails_build_and_verification(self):
        paper = self.fixture.paper()
        optional = self.fixture.document(paper, "notes", ".txt", "hash")
        (self.fixture.root / "docs" / optional["path"]).unlink()
        completed = self.fixture.build()
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn(optional["path"], completed.stdout + completed.stderr)
        report = verify_site(self.fixture.root)
        self.assertTrue(any("Configured document does not exist" in str(error) for error in report["errors"]))

    def test_equal_versions_fail_instead_of_silently_overwriting(self):
        paper = self.fixture.paper(version="2")
        for duplicate_version in ["2", "2.0"]:
            with self.subTest(duplicate_version=duplicate_version):
                duplicate = deepcopy(paper)
                duplicate["version"] = duplicate_version
                self.fixture.catalog["papers"] = [paper, duplicate]
                completed = self.fixture.build()
                self.assertNotEqual(completed.returncode, 0)
                report = verify_site(self.fixture.root)
                self.assertGreater(report["error_count"], 0)
                self.assertEqual(report["errors"][0][0], "catalog")

    def test_missing_supplement_token_fails_instead_of_linking_another_paper(self):
        paper = self.fixture.paper()
        self.fixture.fragments(paper, '<p><a href="{{SUPP_PDF}}">Unconfigured supplement</a></p>')
        completed = self.fixture.build()
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("supplement", (completed.stdout + completed.stderr).lower())

    def test_nonnumeric_versions_require_explicit_order(self):
        draft = self.fixture.paper(version="draft")
        final = self.fixture.paper(version="accepted")
        self.fixture.save()
        with self.assertRaises(ValueError):
            load_catalog(self.fixture.root)
        draft["version_order"] = 1
        final["version_order"] = 2
        self.fixture.catalog["papers"] = [final, draft]
        self.build_successfully()
        report = self.verify_successfully()
        self.assertEqual(report["checks"]["selected_versions"], {"stellar-physics/modes": "accepted"})

    def test_partial_audience_registration_is_rejected(self):
        paper = self.fixture.paper()
        paper["audiences"] = ["general", "expert"]
        self.fixture.save()
        report = verify_site(self.fixture.root)
        self.assertGreater(report["error_count"], 0)
        self.assertIn("audiences", str(report["errors"]))

    def test_distinct_active_papers_cannot_share_article_source_prefix(self):
        first = self.fixture.paper("modes")
        second = self.fixture.paper("vortices")
        second["content_prefix"] = first["content_prefix"]
        completed = self.fixture.build()
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("content_prefix", completed.stdout + completed.stderr)

    def test_document_cannot_overwrite_a_generated_page(self):
        paper = self.fixture.paper()
        document = paper["documents"][0]
        document["path"] = "en/stellar-physics/modes/expert.html"
        self.fixture.write("docs/" + document["path"], (self.fixture.root / document["source_path"]).read_bytes())
        completed = self.fixture.build()
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("en/stellar-physics/modes/expert.html", completed.stdout + completed.stderr)

    def test_sitemap_rejects_a_download_added_to_the_canonical_page_set(self):
        paper = self.fixture.paper()
        self.build_successfully()
        path = self.fixture.root / "docs/sitemap-pages.xml"
        tree = ET.parse(path)
        ns = "{http://www.sitemaps.org/schemas/sitemap/0.9}"
        entry = ET.SubElement(tree.getroot(), ns + "url")
        ET.SubElement(entry, ns + "loc").text = self.fixture.catalog["public_base_url"] + paper["documents"][0]["path"]
        tree.write(path, encoding="utf-8", xml_declaration=True)
        report = verify_site(self.fixture.root)
        self.assertTrue(any("selected canonical HTML pages" in str(error) for error in report["errors"]))

    def test_indexnow_uses_configured_sitemap_and_dry_run_never_opens_network(self):
        self.fixture.paper()
        self.fixture.catalog["sitemap_filename"] = "custom-pages.xml"
        self.build_successfully()
        self.verify_successfully()
        # A conflicting legacy filename must not be read as a fallback.
        self.fixture.write("docs/sitemap.xml", "Not the configured sitemap.\n")
        key = "0123456789abcdef0123456789abcdef"
        base = self.fixture.catalog["public_base_url"]
        self.fixture.write("docs/" + key + ".txt", key + "\n")
        self.fixture.write("site-src/indexnow.json", json.dumps({
            "site_url": base, "key": key, "key_location": base + key + ".txt",
        }))
        with patch.object(submit_indexnow, "build_opener", side_effect=AssertionError("Network is forbidden")):
            payload, actual_base, _, sitemap_url = submit_indexnow.prepare(root=self.fixture.root)
            self.assertEqual(actual_base, base)
            self.assertEqual(sitemap_url, base + "custom-pages.xml")
            self.assertEqual(len(payload["urlList"]), 7)
            self.assertTrue(all(url.endswith(".html") for url in payload["urlList"]))
            capture = io.StringIO()
            with patch.object(submit_indexnow, "ROOT", self.fixture.root), redirect_stdout(capture):
                self.assertEqual(submit_indexnow.main(["--dry-run"]), 0)
            result = json.loads(capture.getvalue())
            self.assertFalse(result["submission_attempted"])
            self.assertEqual(result["network_requests"], 0)
        (self.fixture.root / "docs" / (key + ".txt")).unlink()
        with self.assertRaises(ValueError):
            submit_indexnow.prepare(root=self.fixture.root)


if __name__ == "__main__":
    unittest.main()
