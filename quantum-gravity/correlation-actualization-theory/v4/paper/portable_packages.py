"""Install the shipped wheels for the private, embeddable Windows interpreter."""
from pathlib import Path, PurePosixPath
from hashlib import sha256
import json
import shutil
import sys
import zipfile

dist, runtime=map(lambda s:Path(s).resolve(),sys.argv[1:3])
if runtime!=Path(sys.executable).resolve().parent:
    raise SystemExit("Only the private interpreter can be initialized.")
config=(dist/"distributions.json").read_bytes()
marker=runtime/"wheel-set-sha256"
fingerprint=sha256(config).hexdigest()
if marker.is_file() and marker.read_text("ascii")==fingerprint:sys.exit(0)
packages=runtime/"packages"
packages.mkdir(exist_ok=True)
for row in json.loads(config):
    if row["package"]=="CPython":continue
    path=dist/row["filename"]
    if sha256(path.read_bytes()).hexdigest()!=row["sha256"]:raise ValueError(path.name)
    with zipfile.ZipFile(path) as z:
        for item in z.infolist():
            if item.is_dir():continue
            parts=PurePosixPath(item.filename).parts
            if not parts or ".." in parts or PurePosixPath(item.filename).is_absolute():raise ValueError(item.filename)
            if parts[0].endswith(".data") and len(parts)>2:
                parts=parts[2:] if parts[1] in ("purelib","platlib") else ("wheel-data",row["package"],*parts[1:])
            target=packages.joinpath(*parts).resolve()
            if packages not in target.parents:raise ValueError(item.filename)
            target.parent.mkdir(parents=True,exist_ok=True)
            with z.open(item) as src,target.open("wb") as dst:shutil.copyfileobj(src,dst)
# Isolated embedded Python normally omits the script directory; archived solvers use sibling imports.
(packages/"sitecustomize.py").write_text("import sys, os\nif sys.argv and sys.argv[0]:\n    sys.path.insert(0,os.path.dirname(os.path.abspath(sys.argv[0])))\n","utf8")
(runtime/"python314._pth").write_text("python314.zip\n.\npackages\nimport site\n","ascii")
marker.write_text(fingerprint,"ascii")

