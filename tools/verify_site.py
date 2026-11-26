#!/usr/bin/env python3
"""Verify the selected reading site and the configured publication documents.

This module performs local checks only. Document identity is established only
when an independently configured SHA-256 or original source file is available.
"""
from argparse import ArgumentParser
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlparse
import xml.etree.ElementTree as ET

from bs4 import BeautifulSoup

try:
    from .site_catalog import (
        generated_page_paths, load_catalog, paper_documents, paper_page_path,
        sitemap_filename,
    )
except ImportError:
    from site_catalog import (
        generated_page_paths, load_catalog, paper_documents, paper_page_path,
        sitemap_filename,
    )

ROOT = Path(__file__).resolve().parents[1]
SITEMAP_NAMESPACE = "{http://www.sitemaps.org/schemas/sitemap/0.9}"


def _inside(base, relative):
    target = (base / relative).resolve()
    if not target.is_relative_to(base.resolve()):
        raise ValueError("Path leaves its publication root: " + str(relative))
    return target


def _repository_target(parsed, catalog, root):
    """Map this repository's blob/tree links to local files without networking."""
    prefix = f"/{catalog['owner']}/{catalog['repository']}/"
    if parsed.netloc != "github.com" or not parsed.path.startswith(prefix):
        return None
    rest = unquote(parsed.path[len(prefix):])
    kind, _, rest = rest.partition("/")
    if kind not in {"blob", "tree"} or "/" not in rest:
        return None
    refs = {"main"}
    for paper in catalog["papers"]:
        refs.add(paper.get("source_ref") or paper.get("release") or "main")
    for ref in sorted(refs, key=len, reverse=True):
        if rest.startswith(ref + "/"):
            return _inside(root, rest[len(ref) + 1:])
    # Explicit links to other refs still get a local existence check; fetching
    # those refs and establishing remote identity is a separate publication step.
    return _inside(root, rest.split("/", 1)[1])


def verify_site(root=ROOT):
    """Return a JSON-serializable report without changing files or making requests."""
    root = Path(root).resolve()
    docs = root / "docs"
    errors = []
    checks = {
        "html_pages": 0,
        "article_pages": 0,
        "local_links": 0,
        "paper_source_links": 0,
        "site_verification_files": {},
        "document_sha256": {},
        "document_identity": {},
    }

    def result():
        return {"checks": checks, "error_count": len(errors), "errors": errors}

    try:
        catalog = load_catalog(root)
        languages = catalog["languages"]
        expected_pages = generated_page_paths(catalog)
        sitemap_name = sitemap_filename(catalog)
    except (ValueError, OSError, KeyError, TypeError) as exc:
        errors.append(["catalog", str(exc)])
        return result()
    checks["configured_languages"] = languages
    checks["selected_versions"] = {
        f"{paper['field']}/{paper['slug']}": paper["version"]
        for paper in catalog["papers"]
    }
    checks["sitemap_filename"] = sitemap_name

    ownership_html = set()
    for path in docs.glob("google*.html"):
        if re.fullmatch(r"google[0-9a-f]+\.html", path.name):
            ownership_html.add(path)
            raw = path.read_bytes()
            if raw.strip() != ("google-site-verification: " + path.name).encode("ascii"):
                errors.append([path.name, "Google ownership verification file has unexpected content"])
            checks["site_verification_files"][path.name] = hashlib.sha256(raw).hexdigest()
    bing_file = docs / "BingSiteAuth.xml"
    if bing_file.is_file():
        checks["site_verification_files"][bing_file.name] = hashlib.sha256(bing_file.read_bytes()).hexdigest()

    document_paths = {
        docs / document["path"]
        for paper in catalog["papers"]
        for document in paper_documents(paper)
    }
    pages = {}
    for path in docs.rglob("*.html"):
        if path in ownership_html or path in document_paths or path.name.startswith("_qa"):
            continue
        try:
            pages[path] = BeautifulSoup(path.read_text(encoding="utf-8"), "html.parser")
        except (OSError, UnicodeError) as exc:
            errors.append([str(path.relative_to(docs)), "cannot read HTML", str(exc)])
    actual_pages = {path.relative_to(docs).as_posix() for path in pages}
    if actual_pages != expected_pages:
        errors.append([
            "site pages", "published pages differ from the selected catalog",
            {"missing": sorted(expected_pages - actual_pages), "extra": sorted(actual_pages - expected_pages)},
        ])

    canonical_pages = {}
    alternate_sets = {}
    base = catalog["public_base_url"]
    base_url = urlparse(base)
    for path, soup in pages.items():
        checks["html_pages"] += 1
        rel = path.relative_to(docs).as_posix()
        lang = soup.html.get("lang") if soup.html else None
        if lang not in languages:
            errors.append([rel, "page language is not configured for publication"])
        if len(languages) == 1 and soup.select(".language,.lang-switch"):
            errors.append([rel, "unexpected language switch on a single-language site"])
        canonical = soup.select('head link[rel="canonical"]')
        expected_canonical = base + rel
        if len(canonical) != 1 or canonical[0].get("href") != expected_canonical:
            errors.append([rel, "canonical URL does not match the published page"])
        canonical_pages[expected_canonical] = soup
        alternates = soup.select('head link[rel="alternate"][hreflang]')
        alternate_sets[expected_canonical] = {n["hreflang"]: n.get("href", "") for n in alternates}
        if len(alternate_sets[expected_canonical]) != len(alternates):
            errors.append([rel, "duplicate hreflang language"])
        home = rel == "index.html" or rel in {code + "/index.html" for code in languages}
        expected_languages = set(languages) | {"x-default"} if home else {lang}
        if set(alternate_sets[expected_canonical]) != expected_languages:
            errors.append([rel, "hreflang set does not cover the published language versions"])
        if expected_canonical not in alternate_sets[expected_canonical].values():
            errors.append([rel, "hreflang set omits the page itself"])
        ids = [node["id"] for node in soup.select("[id]")]
        if len(ids) != len(set(ids)):
            errors.append([rel, "duplicate HTML IDs"])
        if len(soup.select("h1")) != 1:
            errors.append([rel, "expected one h1"])
        if soup.select(".katex-error"):
            errors.append([rel, "KaTeX error"])
        if re.search(r"\{\{[^{}]+\}\}|data-figure=", str(soup)):
            errors.append([rel, "unfilled content token"])

        for element in soup.select("[href],script[src],img[src],iframe[src]"):
            link = element.get("href", element.get("src", ""))
            parsed = urlparse(link)
            try:
                if parsed.scheme or parsed.netloc:
                    source_target = _repository_target(parsed, catalog, root)
                    if source_target is not None:
                        checks["paper_source_links"] += 1
                        if not source_target.exists():
                            errors.append([rel, "missing source", str(source_target.relative_to(root))])
                        continue
                    if (parsed.scheme, parsed.netloc) != (base_url.scheme, base_url.netloc):
                        continue
                    if not parsed.path.startswith(base_url.path):
                        continue
                    target = _inside(docs, unquote(parsed.path[len(base_url.path):]))
                elif parsed.path.startswith("/"):
                    if not parsed.path.startswith(base_url.path):
                        errors.append([rel, "local URL is outside the published project", link])
                        continue
                    target = _inside(docs, unquote(parsed.path[len(base_url.path):]))
                else:
                    target = (path.parent / unquote(parsed.path)).resolve() if parsed.path else path
                    if not target.is_relative_to(docs):
                        raise ValueError("Local link leaves docs")
            except ValueError as exc:
                errors.append([rel, "invalid local or source path", link, str(exc)])
                continue
            checks["local_links"] += 1
            if not target.exists():
                errors.append([rel, "missing local file", link])
                continue
            if parsed.fragment and target.suffix == ".html" and target in pages:
                if not pages[target].find(id=unquote(parsed.fragment)):
                    errors.append([rel, "missing fragment", link])

        if soup.select_one(".article-content"):
            checks["article_pages"] += 1
            article = soup.select_one(".article-content article")
            first = article.find(recursive=False) if article is not None else None
            if first is None or "tldr" not in first.get("class", []):
                errors.append([rel, "TL;DR must be first article block"])
            if first is None or not first.h2 or "TL;DR" not in first.h2.get_text():
                errors.append([rel, "missing visible TL;DR heading"])
            for figure in soup.select("figure.diagram"):
                if not figure.select_one("svg title") or not figure.figcaption:
                    errors.append([rel, "unlabelled figure", figure.get("id")])

    checks["hreflang_links"] = 0
    for canonical, alternates in alternate_sets.items():
        for language, target in alternates.items():
            checks["hreflang_links"] += 1
            parsed = urlparse(target)
            if parsed.scheme != "https" or not parsed.netloc:
                errors.append([canonical, "hreflang URL must be absolute HTTPS", target])
            elif target not in canonical_pages:
                errors.append([canonical, "hreflang target has no published canonical page", target])
            else:
                if alternate_sets[target] != alternates:
                    errors.append([canonical, "hreflang targets do not share the same reciprocal set", target])
                target_html = canonical_pages[target].html
                if language != "x-default" and (target_html is None or target_html.get("lang") != language):
                    errors.append([canonical, "hreflang target language differs", language, target])

    try:
        sitemap = ET.parse(docs / sitemap_name)
        if sitemap.getroot().tag != SITEMAP_NAMESPACE + "urlset":
            errors.append([sitemap_name, "incorrect sitemap root or namespace"])
        sitemap_urls = [node.text or "" for node in sitemap.findall(SITEMAP_NAMESPACE + "url/" + SITEMAP_NAMESPACE + "loc")]
        checks["sitemap_urls"] = len(sitemap_urls)
        if len(sitemap_urls) != len(set(sitemap_urls)):
            errors.append([sitemap_name, "duplicate URL"])
        expected_urls = {base + page for page in expected_pages}
        if set(sitemap_urls) != expected_urls:
            errors.append([
                sitemap_name, "URL coverage differs from the selected canonical HTML pages",
                {"missing": sorted(expected_urls - set(sitemap_urls)), "extra": sorted(set(sitemap_urls) - expected_urls)},
            ])
    except (OSError, ET.ParseError) as exc:
        errors.append([sitemap_name, "cannot read a valid XML sitemap", str(exc)])

    for paper in catalog["papers"]:
        for audience in paper["audiences"]:
            for lang in paper["languages"]:
                article = pages.get(docs / paper_page_path(paper, lang, audience))
                if article is None or not article.select_one(".article-content article"):
                    errors.append([paper["slug"], audience, lang, "configured reading guide is missing"])
                elif not article.select("article section"):
                    errors.append([paper["slug"], audience, lang, "reading guide lacks sections"])
        for document in paper_documents(paper):
            key = f"{paper['field']}/{paper['slug']}/v{paper['version']}/{document['id']}"
            identity = {"path": document["path"], "identity": "unchecked", "methods": []}
            checks["document_identity"][key] = identity
            before = len(errors)
            try:
                target = _inside(docs, document["path"])
                if not target.is_file():
                    raise ValueError("Configured document does not exist: " + document["path"])
                published = target.read_bytes()
                digest = hashlib.sha256(published).hexdigest()
                checks["document_sha256"][document["path"]] = digest
                if document.get("sha256"):
                    identity["methods"].append("sha256")
                    if digest != document["sha256"]:
                        errors.append([key, "document differs from its independent SHA-256", document["path"]])
                if document.get("source_path"):
                    identity["methods"].append("source_bytes")
                    source = _inside(root, document["source_path"])
                    if source == target:
                        errors.append([key, "document source must be distinct from the served file", document["source_path"]])
                    elif not source.is_file():
                        errors.append([key, "original document source is missing", document["source_path"]])
                    elif published != source.read_bytes():
                        errors.append([key, "document differs from original source bytes", document["path"], document["source_path"]])
                if identity["methods"]:
                    identity["identity"] = "verified" if len(errors) == before else "failed"
            except (OSError, ValueError) as exc:
                errors.append([key, "document verification failed", str(exc)])
                identity["identity"] = "failed"
    return result()


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="Repository root (also supports isolated test fixtures)")
    args = parser.parse_args(argv)
    report = verify_site(args.root)
    destination = args.root / "site-src/verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    destination.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 1 if report["error_count"] else 0


if __name__ == "__main__":
    sys.exit(main())
