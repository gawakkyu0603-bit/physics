#!/usr/bin/env python3
"""Reconstruct the five frozen CAT v4 release assets, verifying every byte.

Only reads repository/source files and official public upstream URLs. No GitHub
API, credentials, shell commands, dependency installation, or publication.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import sys
import tempfile
import urllib.parse
import urllib.request
import zipfile
import zlib


HERE = Path(__file__).resolve().parent
PAYLOAD_PREFIX = "CAT-review/"
ALLOWED_HOSTS = {
    "files.pythonhosted.org", "www.python.org", "github.com",
    "codeload.github.com", "oleanstorage.azureedge.net",
}
COPY_ASSETS = {
    "CAT_v4_main.pdf": "main.pdf",
    "CAT_v4_supplement.pdf": "supplement.pdf",
    "CAT_v4_article_source.tar.gz": "arxiv-source.tar.gz",
}


class VerificationError(RuntimeError):
    pass


def log(event: str, **fields: object) -> None:
    print(json.dumps({"event": event, **fields}, ensure_ascii=False), flush=True)


def digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def safe_path(root: Path, name: str) -> Path:
    relative = PurePosixPath(name)
    if relative.is_absolute() or ".." in relative.parts or "\\" in name:
        raise VerificationError(f"Unsafe relative path: {name}")
    result = root.joinpath(*relative.parts)
    if not result.resolve().is_relative_to(root.resolve()):
        raise VerificationError(f"Path leaves source directory: {name}")
    return result


def verify(path: Path, record: dict) -> None:
    if not path.is_file():
        raise VerificationError(f"Missing file: {path}")
    actual_size = path.stat().st_size
    if actual_size != record["bytes"]:
        raise VerificationError(
            f"Size mismatch: {path}: {actual_size} != {record['bytes']}")
    actual_hash = digest(path)
    if actual_hash != record["sha256"]:
        raise VerificationError(
            f"SHA256 mismatch: {path}: {actual_hash} != {record['sha256']}")


def load_inputs() -> tuple[dict, dict[str, dict]]:
    inputs = json.loads((HERE / "inputs.json").read_text(encoding="utf-8"))
    manifest_file = HERE / "embedded" / "PUBLICATION_MANIFEST.json"
    if digest(manifest_file) != inputs["publication_manifest_sha256"]:
        raise VerificationError("Frozen publication manifest changed")
    manifest = json.loads(manifest_file.read_bytes())
    if manifest["original_archive_sha256"] != inputs["original_archive_sha256"]:
        raise VerificationError("Original archive identity does not match")
    records = {row["path"]: row for row in manifest["files"]}
    if len(records) != 756 or len(manifest["files"]) != 756:
        raise VerificationError("Expected 756 unique manifest records")
    payload = [name for name in records if name.startswith(PAYLOAD_PREFIX)]
    if len(payload) != inputs["original_files"] or len(payload) != 742:
        raise VerificationError("Expected 742 frozen original files")
    supplements = inputs["upstream"] + inputs["embedded_original_files"]
    if len({row["path"] for row in supplements}) != 33:
        raise VerificationError("Expected 33 distinct original supplements")
    for row in supplements:
        if {k: row[k] for k in ("path", "bytes", "sha256")} != records[row["path"]]:
            raise VerificationError(f"Supplement differs from original: {row['path']}")
    records["PUBLICATION_MANIFEST.json"] = {
        "path": "PUBLICATION_MANIFEST.json",
        "bytes": manifest_file.stat().st_size,
        "sha256": inputs["publication_manifest_sha256"],
    }
    return inputs, records


def fetch_one(row: dict, cache: Path) -> dict:
    target = cache / row["sha256"]
    if target.is_file():
        verify(target, row)
        log("upstream-cache-verified", path=row["path"], bytes=row["bytes"])
        return {"path": row["path"], "sha256": row["sha256"], "cached": True}
    url = urllib.parse.urlsplit(row["url"])
    if url.scheme != "https" or url.hostname not in ALLOWED_HOSTS:
        raise VerificationError(f"URL is not an allowlisted official source: {row['url']}")
    request = urllib.request.Request(
        row["url"], headers={"User-Agent": "CAT-v4-byte-verified-release-builder/1"})
    fd, tmp_name = tempfile.mkstemp(prefix="download-", suffix=".part", dir=cache)
    temporary = Path(tmp_name)
    try:
        with os.fdopen(fd, "wb") as output:
            with urllib.request.urlopen(request, timeout=120) as response:
                if urllib.parse.urlsplit(response.url).scheme != "https":
                    raise VerificationError("Upstream redirected away from HTTPS")
                while True:
                    block = response.read(1024 * 1024)
                    if not block:
                        break
                    output.write(block)
                    if output.tell() > row["bytes"]:
                        raise VerificationError(f"Upstream size exceeded pin: {row['path']}")
        verify(temporary, row)
        temporary.replace(target)
    finally:
        temporary.unlink(missing_ok=True)
    log("upstream-downloaded-verified", path=row["path"], bytes=row["bytes"])
    return {"path": row["path"], "sha256": row["sha256"], "cached": False}


def fetch_all(inputs: dict, cache: Path, workers: int) -> list[dict]:
    cache.mkdir(parents=True, exist_ok=True)
    # Several universal Python wheels are identical on Linux and Windows.
    unique = {row["sha256"]: row for row in inputs["upstream"]}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as executor:
        results = list(executor.map(lambda row: fetch_one(row, cache), unique.values()))
    log("upstream-complete", paths=len(inputs["upstream"]), unique=len(unique))
    return results


def assemble_sources(inputs: dict, records: dict[str, dict], args) -> dict[str, Path]:
    downloads = {row["path"]: row for row in inputs["upstream"]}
    embedded = {row["path"] for row in inputs["embedded_original_files"]}
    sources = {}
    for name, record in sorted(records.items()):
        if not name.startswith(PAYLOAD_PREFIX):
            source = safe_path(HERE / "embedded", name)
        elif args.local_full_root:
            source = safe_path(args.local_full_root, name[len(PAYLOAD_PREFIX):])
        elif name in embedded:
            source = safe_path(HERE / "embedded", name)
        elif name in downloads:
            source = args.cache / downloads[name]["sha256"]
        else:
            source = safe_path(args.paper_root, name[len(PAYLOAD_PREFIX):])
        verify(source, record)
        sources[name] = source
    log("all-inputs-verified", files=len(sources), original_files=742,
        retained_in_git=709, embedded_original_files=2, upstream_files=31)
    return sources


def build(inputs: dict, records: dict[str, dict], args) -> dict:
    sources = assemble_sources(inputs, records, args)
    assets = {row["name"]: row for row in inputs["assets"]}
    args.output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".release-build-", dir=args.output) as directory:
        staging = Path(directory)
        destination = staging / "CAT_v4_full_publication_bundle.zip"
        settings = inputs["zip"]
        with zipfile.ZipFile(destination, "w", compression=zipfile.ZIP_DEFLATED,
                             compresslevel=settings["compresslevel"]) as archive:
            for name, source in sorted(sources.items()):
                entry = zipfile.ZipInfo(name, date_time=tuple(settings["date_time"]))
                entry.create_system = settings["create_system"]
                entry.compress_type = zipfile.ZIP_DEFLATED
                entry.external_attr = settings["external_attr"]
                archive.writestr(entry, source.read_bytes(),
                                 compress_type=zipfile.ZIP_DEFLATED,
                                 compresslevel=settings["compresslevel"])
        verify(destination, assets[destination.name])
        for filename, original in COPY_ASSETS.items():
            shutil.copyfile(sources[PAYLOAD_PREFIX + original], staging / filename)
        shutil.copyfile(HERE / "SHA256SUMS", staging / "SHA256SUMS")
        for filename, record in assets.items():
            verify(staging / filename, record)
        # No final asset is installed until all five expected hashes match.
        for filename in assets:
            (staging / filename).replace(args.output / filename)
    result = {
        "status": "all_five_assets_byte_identical",
        "python": sys.version,
        "zlib_compile_version": zlib.ZLIB_VERSION,
        "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
        "original_files_verified": 742,
        "zip_members": len(sources),
        "assets": list(assets.values()),
    }
    (args.output / "build-report.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    log("build-complete", **result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper-root", type=Path,
                        default=Path("quantum-gravity/correlation-actualization-theory/v4/paper"))
    parser.add_argument("--local-full-root", type=Path,
                        help="Offline validation against all 742 extracted original files")
    parser.add_argument("--cache", type=Path, default=HERE / ".upstream-cache")
    parser.add_argument("--output", type=Path, default=HERE / "dist")
    parser.add_argument("--download", action="store_true",
                        help="Fetch exact hash-pinned files from official public URLs")
    parser.add_argument("--fetch-only", action="store_true")
    parser.add_argument("--workers", type=int, default=4, choices=range(1, 9))
    args = parser.parse_args()
    inputs, records = load_inputs()
    log("runtime", python=sys.version.split()[0], zlib_compile=zlib.ZLIB_VERSION,
        zlib_runtime=zlib.ZLIB_RUNTIME_VERSION)
    if args.download or args.fetch_only:
        results = fetch_all(inputs, args.cache, args.workers)
        (args.cache / "verification.json").write_text(
            json.dumps(results, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    if not args.fetch_only:
        build(inputs, records, args)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, VerificationError) as error:
        log("failed", error=str(error))
        sys.exit(1)
