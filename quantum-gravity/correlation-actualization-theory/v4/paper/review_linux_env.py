"""Unpack the checksum-pinned Linux wheels for the local CPython, without changing that Python."""
from pathlib import Path, PurePosixPath
import sys, platform, json, hashlib, shutil, zipfile

if sys.version_info[:2]!=(3,12) or sys.platform!="linux" or platform.machine()!="x86_64":
    raise SystemExit("The shipped native wheels target Linux x86_64 with CPython 3.12.")
root=Path(__file__).resolve().parent
dist=root/"evidence/python-linux"
cache=Path(sys.argv[1]).resolve()
target=cache/"site"
target.mkdir(parents=True,exist_ok=True)
spec=(dist/"distributions.json").read_bytes()
digest=hashlib.sha256(spec).hexdigest()
marker=target/"installed.sha256"
if marker.is_file() and marker.read_text("ascii")==digest:sys.exit(0)
for row in json.loads(spec):
    path=dist/row["filename"]
    if hashlib.sha256(path.read_bytes()).hexdigest()!=row["sha256"]:raise ValueError("Wheel checksum: "+path.name)
    with zipfile.ZipFile(path) as z:
        for entry in z.infolist():
            if entry.is_dir(): continue
            parts=PurePosixPath(entry.filename).parts
            if not parts or ".." in parts or entry.filename.startswith("/"):raise ValueError(entry.filename)
            if parts[0].endswith(".data") and len(parts)>2:
                parts=parts[2:] if parts[1] in ("purelib","platlib") else ("wheel-data",row["package"],*parts[1:])
            dest=target.joinpath(*parts).resolve()
            if target not in dest.parents:raise ValueError(entry.filename)
            dest.parent.mkdir(parents=True,exist_ok=True)
            with z.open(entry) as src,dest.open("wb") as dst:shutil.copyfileobj(src,dst)
marker.write_text(digest,"ascii")

