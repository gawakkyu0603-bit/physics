#!/usr/bin/env python3
"""Import an explicitly approved, checksum-pinned research ZIP without executing it."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import tempfile
import re
import xml.etree.ElementTree as ET
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

def convert_pdf_figure(raw, identifier, caption):
    """Convert an approved one-page source figure to an accessible inline SVG.

    Namespaced IDs prevent collisions when several plots share one HTML page.
    The source PDF and its expected checksum are unchanged.
    """
    if not re.fullmatch(r"[a-z0-9-]+", identifier):
        raise ValueError(f"Invalid figure ID: {identifier}")
    svg_ns = "http://www.w3.org/2000/svg"
    xlink_ns = "http://www.w3.org/1999/xlink"
    ET.register_namespace("", svg_ns)
    ET.register_namespace("xlink", xlink_ns)
    with tempfile.TemporaryDirectory() as tmp:
        inp = Path(tmp) / "source.pdf"
        out = Path(tmp) / "figure.svg"
        inp.write_bytes(raw)
        subprocess.run(["pdftocairo", "-svg", str(inp), str(out)], check=True, timeout=60)
        svg = ET.parse(out).getroot()
    if svg.tag != "{" + svg_ns + "}svg" or not svg.get("viewBox"):
        raise ValueError(f"Invalid SVG from {identifier}")
    mapping = {node.get("id"): identifier + "-" + node.get("id") for node in svg.iter() if node.get("id")}
    for node in svg.iter():
        for key, value in list(node.attrib.items()):
            if key == "id":
                node.set(key, mapping[value])
            elif value.startswith("#") and value[1:] in mapping:
                node.set(key, "#" + mapping[value[1:]])
            else:
                node.set(key, re.sub(r"url\(#([^)]*)\)", lambda m: "url(#" + mapping.get(m[1], m[1]) + ")", value))
    for attr in ("width", "height"):
        svg.attrib.pop(attr, None)
    title_id = identifier + "-title"
    svg.set("role", "img")
    svg.set("aria-labelledby", title_id)
    title = ET.Element("{" + svg_ns + "}title", {"id": title_id})
    title.text = caption["title"] + ". " + caption["description"]
    svg.insert(0, title)
    return ET.tostring(svg, encoding="utf-8") + b"\n"

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
    if not destination.is_dir() and not spec.get("activate_paper"):
        raise ValueError("Unknown research destination")
    prefix = spec.get("source_prefix", "")
    if prefix and (not prefix.endswith("/") or "/" in prefix[:-1] or prefix in ("./", "../")):
        raise ValueError("Invalid archive root prefix")
    excluded = set(spec.get("exclude", []))
    if not excluded <= set(expected):
        raise ValueError("Excluded path is not in the approved archive")
    data = {}
    with zipfile.ZipFile(archive) as bundle:
        infos = bundle.infolist()
        if len(infos) != len(expected) or {i.filename for i in infos} != {prefix + name for name in expected}:
            raise ValueError("Archive entries differ from approved files")
        if sum(i.file_size for i in infos) > 100 * 1024**2:
            raise ValueError("Uncompressed files exceed limit")
        for info in infos:
            mode = info.external_attr >> 16
            if info.is_dir() or stat.S_ISLNK(mode):
                raise ValueError("Only regular approved files may be imported")
            relative = info.filename[len(prefix):]
            out = target(destination, relative)
            raw = bundle.read(info)
            if digest(raw) != expected[relative]:
                raise ValueError(f"Research-file SHA-256 mismatch: {info.filename}")
            if relative in excluded:
                continue
            if out.exists() and (not out.is_file() or out.read_bytes() != raw):
                raise ValueError(f"Refusing to overwrite different existing research: {out}")
            data[out] = raw
    catalog_path = root / "site-src/catalog.json"
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    matches = [p for p in catalog["papers"] if all(str(p.get(k)) == str(v) for k,v in spec["paper"].items())]
    if spec.get("activate_paper"):
        if matches:
            raise ValueError("Refusing to activate an already registered manuscript")
        paper = spec["activate_paper"]
        if not all(str(paper.get(k)) == str(v) for k, v in spec["paper"].items()):
            raise ValueError("Activation does not match the approved paper")
        catalog["papers"].append(paper)
    else:
        if len(matches) != 1:
            raise ValueError("Expected one matching paper")
        paper = matches[0]
    for related in spec.get("series_updates", []):
        found = [p for p in catalog["papers"] if all(str(p.get(k)) == str(v) for k, v in related["paper"].items())]
        if len(found) != 1:
            raise ValueError("Research series member is missing or ambiguous")
        for key in ("series", "series_order"):
            if key in found[0] and found[0][key] != related[key]:
                raise ValueError("Conflicting research series assignment")
            found[0][key] = related[key]
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
    additions = {}
    for item in spec.get("additional_text_files", []):
        out = target(root, item["path"])
        if not out.is_relative_to(destination.parent) or out.exists() or out in data or out in edits or out in additions:
            raise ValueError(f"Invalid additional paper documentation: {out}")
        additions[out] = item["content"].encode("utf-8")
    for figure in spec.get("web_figures", []):
        source = target(destination, figure["source"])
        if source not in data or source.suffix.lower() != ".pdf":
            raise ValueError("Figure source is not an approved original PDF")
        identifier = figure["id"]
        caption = {"title": figure["title"], "description": figure["description"]}
        svg = convert_pdf_figure(data[source], identifier, caption)
        for suffix, raw in ((".svg", svg), (".json", (json.dumps(caption, ensure_ascii=False, indent=2) + "\n").encode("utf-8"))):
            out = target(root, "site-src/figures/" + identifier + suffix)
            if out.exists() or out in additions:
                raise ValueError(f"Refusing to overwrite a registered figure: {out}")
            additions[out] = raw
    # Every input, original byte identity, destination, figure and edit has been checked.
    for out, raw in {**data, **additions}.items():
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_bytes(raw)
    for out, rendered in edits.items():
        out.write_text(rendered, encoding="utf-8")
    (destination / "README.md").write_text(spec["readme"], encoding="utf-8")
    (destination / "SHA256SUMS").write_text("".join(f"{item['sha256']}  {item['path']}\n" for item in spec["files"] if item["path"] not in excluded), encoding="utf-8")
    if excluded:
        print(f"Checked {len(expected)} archive entries; omitted {len(excluded)} designated editorial/planning files")
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
