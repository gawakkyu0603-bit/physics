#!/usr/bin/env python3
"""Validate published sitemap URLs and submit one IndexNow notification to Bing.

No requests are made with --dry-run. Normal mode checks the live public key
and sitemap before a single POST; it never retries automatically.
"""
from argparse import ArgumentParser
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import sys
from urllib.error import HTTPError, URLError
from urllib.parse import unquote, urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener
import xml.etree.ElementTree as ET

try:
    from .site_catalog import load_catalog, sitemap_filename
except ImportError:
    from site_catalog import load_catalog, sitemap_filename

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "https://www.bing.com/indexnow"
SITEMAP_NAMESPACE = "{http://www.sitemaps.org/schemas/sitemap/0.9}"


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def scoped_url(value, base, root=ROOT):
    """Require a canonical static URL within the configured project directory."""
    parsed, scope = urlsplit(value), urlsplit(base)
    if (parsed.scheme != "https" or parsed.netloc != scope.netloc
            or parsed.username or parsed.password or parsed.query or parsed.fragment
            or not parsed.path.startswith(scope.path)
            or any(part in {".", ".."} for part in unquote(parsed.path).split("/"))):
        raise ValueError("URL is outside the configured HTTPS project scope: " + value)
    relative = unquote(parsed.path[len(scope.path):])
    local = (root / "docs" / relative).resolve()
    if not local.is_relative_to((root / "docs").resolve()) or not local.is_file():
        raise ValueError("URL does not map to a published local file: " + value)
    return local


def sitemap_urls(data):
    root = ET.fromstring(data)
    if root.tag != SITEMAP_NAMESPACE + "urlset":
        raise ValueError("Expected a sitemap urlset with the standard namespace")
    urls = [node.text or "" for node in root.findall(
        SITEMAP_NAMESPACE + "url/" + SITEMAP_NAMESPACE + "loc")]
    if not urls or len(urls) != len(set(urls)):
        raise ValueError("The sitemap must contain nonempty, unique URLs")
    return urls


def prepare(selected_urls=None, root=ROOT):
    root = Path(root)
    catalog = load_catalog(root)
    config = json.loads((root / "site-src/indexnow.json").read_text())
    base = catalog["public_base_url"]
    scope = urlsplit(base)
    if (scope.scheme != "https" or not scope.netloc or scope.username or scope.password
            or scope.port is not None or scope.query or scope.fragment
            or not scope.path.endswith("/") or config["site_url"] != base):
        raise ValueError("IndexNow site_url must match the HTTPS catalog public_base_url")
    key = config["key"]
    if not re.fullmatch(r"[0-9a-f]{32}", key):
        raise ValueError("The persisted public verification key must be 32 lowercase hex characters")
    key_location = config["key_location"]
    if key_location != base + key + ".txt":
        raise ValueError("key_location must identify the key file at the project root")
    key_path = scoped_url(key_location, base, root)
    if key_path.read_text(encoding="utf-8").strip() != key:
        raise ValueError("The local verification file differs from the configured key")
    sitemap_name = sitemap_filename(catalog)
    sitemap_data = (root / "docs" / sitemap_name).read_bytes()
    urls = sitemap_urls(sitemap_data)
    for url in urls:
        scoped_url(url, base, root)
    if key_location in urls:
        raise ValueError("Do not include the verification key file in the sitemap")
    if selected_urls:
        if len(selected_urls) != len(set(selected_urls)):
            raise ValueError("--url arguments must not contain duplicates")
        if not set(selected_urls).issubset(urls):
            raise ValueError("Every --url must already be in the validated sitemap")
        urls = selected_urls
    if len(urls) > 10000:
        raise ValueError("IndexNow allows at most 10,000 URLs per POST; select a smaller set")
    payload = {"host": scope.hostname, "key": key,
               "keyLocation": key_location, "urlList": urls}
    return payload, base, sitemap_data, base + sitemap_name


def request_bytes(opener, request, limit):
    with opener.open(request, timeout=30) as response:
        data = response.read(limit + 1)
        if len(data) > limit:
            raise ValueError("Response exceeds the expected size")
        return response.status, data


def main(argv=None):
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="Validate locally; make no network requests")
    parser.add_argument("--url", action="append", help="Submit only this sitemap URL; repeat for more URLs")
    parser.add_argument("--output", type=Path, help="Save the JSON result to this path")
    args = parser.parse_args(argv)
    result = {"timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "endpoint": ENDPOINT, "dry_run": args.dry_run,
              "submission_attempted": False, "http_status": None,
              "indexing_status": "not_checked", "automatic_retries": 0}
    exit_code = 1
    try:
        payload, base, local_sitemap, sitemap_url = prepare(args.url, ROOT)
        result.update({"site_url": base, "url_count": len(payload["urlList"]),
                       "urls": payload["urlList"], "key_location": payload["keyLocation"],
                       "sitemap_url": sitemap_url})
        if args.dry_run:
            result.update({"result": "dry_run_validated", "network_requests": 0})
            exit_code = 0
        else:
            opener = build_opener(NoRedirect())
            headers = {"User-Agent": "physics-research-indexnow/1.0"}
            status, live_key = request_bytes(opener, Request(payload["keyLocation"], headers=headers), 1024)
            if status != 200 or live_key.decode("utf-8").strip() != payload["key"]:
                raise ValueError("The live public verification key does not match; deploy before submitting")
            result["key_verified_live"] = True
            status, live_sitemap = request_bytes(opener, Request(sitemap_url, headers=headers), 50 * 1024 * 1024)
            if status != 200 or set(sitemap_urls(live_sitemap)) != set(sitemap_urls(local_sitemap)):
                raise ValueError("The live sitemap differs from this checkout; finish deployment before submitting")
            result["sitemap_matches_live"] = True
            request = Request(ENDPOINT, data=json.dumps(payload).encode("utf-8"), method="POST",
                              headers={**headers, "Content-Type": "application/json; charset=utf-8"})
            result["submission_attempted"] = True
            status, response = request_bytes(opener, request, 65536)
            result["http_status"] = status
            if response:
                result["response_excerpt"] = response.decode("utf-8", errors="replace")[:512]
            if status == 200:
                result["result"] = "received"
                exit_code = 0
            elif status == 202:
                result["result"] = "received_key_verification_pending"
                exit_code = 0
            else:
                result["result"] = "unexpected_response"
    except HTTPError as exc:
        result.update({"result": "http_error", "failed_http_status": exc.code,
                       "error": str(exc)})
        if result["submission_attempted"]:
            result["http_status"] = exc.code
    except (ValueError, OSError, URLError, ET.ParseError, KeyError) as exc:
        result.update({"result": "validation_or_network_error", "error": str(exc)})
    rendered = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
