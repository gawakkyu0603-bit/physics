#!/usr/bin/env python3
"""Verify all explicitly approved archives before replacing current manuscripts.
The caller commits the disposable checkout only after all build checks succeed.
No uploaded research code is executed.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import stat
import zipfile
from import_public_bundle import convert_pdf_figure, target

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def put(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    if path.read_bytes() != raw:
        raise ValueError(f"Write identity failed: {path}")

def prep(root, spec):
    arc = target(root, spec["archive"])
    raw = arc.read_bytes()
    if len(raw) > 20 * 1024**2 or digest(raw) != spec["archive_sha256"]:
        raise ValueError(f"Unapproved archive: {arc.name}")
    dest = target(root, spec["destination"])
    if spec["paper"]["source_path"] != spec["destination"] or not dest.is_relative_to(root / "quantum-gravity"):
        raise ValueError("Unexpected research directory")
    old = spec.get("old_pdf_sha256")
    if old:
        if digest((dest / "paper/main.pdf").read_bytes()) != old:
            raise ValueError("Current manuscript changed; refusing replacement")
    elif dest.exists():
        raise ValueError(f"New research directory already exists: {dest}")
    prefix=spec["source_prefix"]
    entries, hashes = {}, {}
    with zipfile.ZipFile(arc) as z:
        infos=z.infolist()
        if len(infos)!=spec["archive_count"] or sum(x.file_size for x in infos)>100*1024**2:
            raise ValueError("Unexpected ZIP count or expanded size")
        for info in infos:
            if info.is_dir() or stat.S_ISLNK(info.external_attr >> 16) or not info.filename.startswith(prefix):
                raise ValueError(f"Unexpected member: {info.filename}")
            rel=info.filename[len(prefix):]
            if not rel or PurePosixPath(rel).as_posix()!=rel or rel in hashes:
                raise ValueError(f"Noncanonical or duplicate member: {rel}")
            target(dest,rel)
            b=z.read(info)
            hashes[rel]=digest(b)
            if rel not in spec["exclude"]:
                entries[rel]=b
        if set(spec["exclude"])-hashes.keys():
            raise ValueError("Missing designated editorial/planning file")
    required={"paper/main.pdf","paper/main.tex","paper/references.bib","PRIOR_ART.md","VERIFICATION.md",spec["script"],"docs/numerical_verification.json"}
    if not required<=entries.keys():
        raise ValueError("Required materials absent")
    document=dict(spec["document"])
    if document["sha256"]!=digest(entries["paper/main.pdf"]) or document["source_path"]!=spec["destination"]+"/paper/main.pdf":
        raise ValueError("Unexpected manuscript bytes or source path")
    edited={}
    for rel in ("PRIOR_ART.md","VERIFICATION.md"):
        b=entries[rel]
        t=b.decode("utf-8").replace(" (Round-5 Independent Re-Review Minor Revision)","").replace("provisional public PDF:","public PDF:")
        b2=t.encode("utf-8")
        if b2!=b:
            edited[rel]={"archive_sha256":digest(b),"published_sha256":digest(b2)}
            entries[rel]=b2
    preserved={}
    for rel in spec["preserve"]:
        path=target(dest,rel)
        if rel in entries or not path.is_file():
            raise ValueError(f"Unexpected preserved asset: {rel}")
        preserved[rel]=path.read_bytes()
    converted={}
    for f in spec["figures"]:
        ident=f["id"]
        caption={"title":f["title"],"description":f["description"]}
        converted["site-src/figures/"+ident+".svg"]=convert_pdf_figure(entries[f["source"]],ident,caption)
        converted["site-src/figures/"+ident+".json"]=(json.dumps(caption,ensure_ascii=False,indent=2)+"\n").encode()
    return dict(spec=spec,arc=arc,dest=dest,entries=entries,hashes=hashes,edited=edited,preserved=preserved,converted=converted,document=document)

def run(root, path):
    batch=json.loads(path.read_text(encoding="utf-8"))
    specs=batch["papers"]
    existing=[target(root,s["archive"]).is_file() for s in specs]
    if not any(existing):
        print("No approved batch uploads present")
        return
    if not all(existing):
        raise ValueError("Incomplete approved collection; refusing partial replacement")
    cp=root/"site-src/catalog.json"
    catalog=json.loads(cp.read_text(encoding="utf-8"))
    oldpapers={p["slug"]:p for p in catalog["papers"]}
    plans=[prep(root,s) for s in specs]
    assert len({p["dest"] for p in plans})==len(plans)
    assert len({p["document"]["path"] for p in plans})==len(plans)
    for plan in plans:
        s=plan["spec"]
        old=oldpapers.get(s["paper"]["slug"])
        if s.get("old_pdf_sha256"):
            if not old or old["source_path"]!=s["destination"] or old["documents"][0]["path"]!=plan["document"]["path"]:
                raise ValueError("Public PDF URL or source path changed")
        elif old:
            raise ValueError("New paper already registered")
    reports=[]
    for plan in plans:
        s,dest,entries=plan["spec"],plan["dest"],plan["entries"]
        if dest.exists():
            shutil.rmtree(dest)
        for rel,data in {**entries,**plan["preserved"]}.items():
            out=target(dest,rel)
            put(out,data)
            if rel.endswith(".sh"):
                out.chmod(0o755)
        put(dest/"README.md",s["readme"].encode())
        published={rel:digest((dest/rel).read_bytes()) for rel in entries}
        put(dest/"SHA256SUMS",("".join(f"{sha}  {rel}\n" for rel,sha in sorted(published.items()))).encode())
        unchanged=sum(published[rel]==plan["hashes"][rel] for rel in entries)
        if unchanged!=len(entries)-len(plan["edited"]):
            raise ValueError("Unexpected original-file change")
        put(dest.parent/"README.md",s["overview_readme"].encode())
        for rel,raw in plan["converted"].items():
            put(target(root,rel),raw)
        paper=s["paper"]
        paper["documents"]=[plan["document"]]
        rec={"slug":paper["slug"],"archive":s["archive"],"archive_sha256":s["archive_sha256"],"archive_entries":len(plan["hashes"]),"published_files":len(entries),"unchanged_originals":unchanged,"excluded":s["exclude"],"editorial_only":plan["edited"],"pdf_sha256":plan["document"]["sha256"],"pdf_bytes":len(entries["paper/main.pdf"]),"files":published}
        reports.append(rec)
        print(f"Imported {paper['slug']}: {len(entries)} research files, {unchanged} byte-identical originals; PDF {rec['pdf_sha256']}")
    selected={x["spec"]["paper"]["slug"] for x in plans}
    catalog["papers"]=[x["spec"]["paper"] for x in plans]+[p for p in catalog["papers"] if p["slug"] not in selected]
    put(cp,(json.dumps(catalog,ensure_ascii=False,indent=2)+"\n").encode())
    put(root/"README.md",batch["root_readme"].encode())
    put(root/"quantum-gravity/README.md",batch["field_readme"].encode())
    put(root/"site-src/import-report.json",(json.dumps(reports,ensure_ascii=False,indent=2)+"\n").encode())
    for plan in plans:
        plan["arc"].unlink()
    print("All approved archives checked and all three temporary ZIPs removed.")

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest",type=Path)
    parser.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
    args=parser.parse_args()
    run(args.root.resolve(),args.manifest.resolve())
