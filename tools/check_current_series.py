#!/usr/bin/env python3
"""Check stable links, current source trees, identities and public text."""
import hashlib
import json
from pathlib import Path
import re
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[1]
cat=json.loads((ROOT/"site-src/catalog.json").read_text())
batch=json.loads((ROOT/"site-src/imports/ostqd-current-series.json").read_text())
report=json.loads((ROOT/"site-src/import-report.json").read_text())
papers=[p for p in cat["papers"] if p.get("series")=="ostqd"]
assert [p["series_order"] for p in papers]==[1,2,3]
assert [p["slug"] for p in papers]==["ostqd","ostqd-sk-jt","ostqd-layer2-type2"]
assert [p["documents"][0]["path"] for p in papers]==["downloads/ostqd.pdf","downloads/ostqd-sk-jt.pdf","downloads/ostqd-layer2-type2.pdf"]
assert len(report)==len(batch["papers"])==3
for spec,rec in zip(batch["papers"],report):
    assert spec["archive_sha256"]==rec["archive_sha256"]
    assert not (ROOT/spec["archive"]).exists()
    dest=ROOT/spec["destination"]
    for rel,sha in rec["files"].items():
        assert hashlib.sha256((dest/rel).read_bytes()).hexdigest()==sha, rel
    assert (ROOT/"docs"/spec["document"]["path"]).read_bytes()==(dest/"paper/main.pdf").read_bytes()
    actual={x.relative_to(dest).as_posix() for x in dest.rglob("*") if x.is_file()}
    assert actual==set(rec["files"])|set(spec["preserve"])|{"README.md","SHA256SUMS"}, spec["destination"]
pattern=re.compile(r"(?i)\b(?:current version:|version\s+\d+|reviewer|referee|peer[- ]review|revision history|review response|round[- ]\d+)\b")
pages=[x for x in (ROOT/"docs").rglob("*.html") if not x.name.startswith("google")]
for x in pages:
    soup=BeautifulSoup(x.read_text(),"html.parser")
    for svg in soup.find_all("svg"):
        svg.decompose()
    assert not pattern.search(soup.get_text(" ",strip=True)), x
for rel in ("index.html","en/index.html","en/quantum-gravity/index.html"):
    soup=BeautifulSoup((ROOT/"docs"/rel).read_text(),"html.parser")
    labels=[li.get_text(" ",strip=True) for li in soup.select(".paper-index h3")]
    assert [re.match(r"Paper (\d+) —",s).group(1) for s in labels]==["1","2","3"], rel
assert len(pages)==15,len(pages)
print("Verified stable PDF URLs, series order, 15 public HTML pages, and all imported file identities.")
