#!/usr/bin/env python3
"""Dispatch explicitly approved single-paper and batch uploads.
No research code is executed; each import requires its pinned archive identity.
"""
import json
from pathlib import Path
from import_current_series import run as run_batch
from import_public_bundle import load as run_single

ROOT=Path(__file__).resolve().parents[1]
for manifest in sorted((ROOT/"site-src/imports").glob("*.json")):
    spec=json.loads(manifest.read_text(encoding="utf-8"))
    if isinstance(spec.get("papers"),list):
        present=any((ROOT/p["archive"]).is_file() for p in spec["papers"])
        run_batch(ROOT,manifest)
        if present and manifest.name=="ostqd-current-series.json":
            Path("/tmp/ostqd-current-series-imported").touch()
    elif "archive" in spec:
        run_single(ROOT,manifest)
    else:
        raise ValueError(f"Unknown approved import manifest: {manifest}")
