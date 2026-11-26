#!/usr/bin/env python3
"""Import an explicitly approved, checksum-pinned research ZIP without executing it."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import zipfile

def digest(data):
    return hashlib.sha256(data).hexdigest()

def target(root, relative):
    posix = PurePosixPath(relative)
    if posix.is_absolute() or ".." in posix.parts or "\\" in relative or not posix.parts:
        raise ValueError(f"Unsafe path: {relative}")
    out = root / posix
    if not out.resolve().is_relative_to(root) or any(p.is_symlink() for p in (out, *out.parents) if p != root and p.is_relative_to(root)):
        raise ValueError(f"Path escapes root or uses symlink: {relative}")
    return out

def load(root, manifest):
    spec = json.loads(manifest.read_text(encoding="utf-8"))
    archive = target(root, spec["archive"])
    if not archive.is_file():
        print("No approved upload present:", spec["archive"])
        return False
    if archive.stat().st_size > 20 * 1024**2:
        raise ValueError("Archive too large for this import")
    if digest(archive.read_bytes()) != spec["archive_sha256"]:
        raise ValueError("Archive SHA-256 does not match the approved public bundle")
    destination = target(root, spec["destination"])
    expected = {item["path"]: item["sha256"] for item in spec["files"]}
    if len(expected) != len(spec["files"]):
        raise ValueError("Duplicate manifest path")
    if not destination.is_dir():
        raise ValueError("Unknown research destination")
    data = {}
    with zipfile.ZipFile(archive) as bundle:
        infos = bundle.infolist()
        if len(infos) != len(expected) or {i.filename for i in infos} != set(expected):
            raise ValueError("Archive entries differ from approved public files")
        if sum(i.file_size for i in infos) > 100 * 1024**2:
            raise ValueError("Uncompressed files exceed limit")
        for info in infos:
            mode = info.external_attr >> 16
            if info.is_dir() or stat.S_ISLNK(mode):
                raise ValueError("Only regular approved files may be imported")
            out = target(destination, info.filename)
            raw = bundle.read(info)
            if digest(raw) != expected[info.filename]:
                raise ValueError(f"Research-file SHA-256 mismatch: {info.filename}")
            if out.exists() and (not out.is_file() or out.read_bytes() != raw):
                raise ValueError(f"Refusing to overwrite different existing research: {out}")
            data[out] = raw
    catalog_path = root / "site-src/catalog.json"
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    matches = [p for p in catalog["papers"] if all(str(p.get(k)) == str(v) for k,v in spec["paper"].items())]
    if len(matches) != 1:
        raise ValueError("Expected one matching paper")
    paper = matches[0]
    if paper.get("source_path") != spec["destination"]:
        raise ValueError("Paper source destination mismatch")
    document = spec["document"]
    original = target(root, document["source_path"])
    if original not in data or digest(data[original]) != document["sha256"]:
        raise ValueError("Registered manuscript does not match approved bytes")
    if any(d["id"] == document["id"] and d != document for d in paper.get("documents", [])):
        raise ValueError("Document registration conflict")
    paper["documents"] = [d for d in paper.get("documents", []) if d["id"] != document["id"]] + [document]
    paper["downloads_intro"] = "Read the original manuscript or explore its source files and reproduction materials."
    edits = {}
    for edit in spec["readme_replacements"]:
        path = target(root, edit["path"])
        original_text = path.read_text(encoding="utf-8")
        if original_text.count(edit["old"]) != 1:
            raise ValueError(f"Expected exactly one README insertion point: {path}")
        edits[path] = original_text.replace(edit["old"], edit["new"], 1)
    # Every input, original byte identity, destination and edit has been checked.
    for out, raw in data.items():
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(raw)
    for out, rendered in edits.items():
        out.write_text(rendered, encoding="utf-8")
    (destination / "README.md").write_text(spec["readme"], encoding="utf-8")
    (destination / "SHA256SUMS").write_text("".join(f"{item['sha256']}  {item['path']}\n" for item in spec["files"]), encoding="utf-8")
    catalog_path.write_text(json.dumps(catalog, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    archive.unlink()
    print(f"Imported {len(data)} original files with matching SHA-256")
    return True

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    load(root, args.manifest.resolve())

if __name__ == "__main__":
    main()
