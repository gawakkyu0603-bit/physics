#!/usr/bin/env python3
"""Verify that the existing release tag contains all 709 frozen Git files."""
from __future__ import annotations

import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile

from build_release import PAYLOAD_PREFIX, VerificationError, load_inputs, log


REPOSITORY = "gawakkyu0603-bit/physics"
TAG = "cat-v4.0.0"
PAPER_ROOT = "quantum-gravity/correlation-actualization-theory/v4/paper"


def verify_tag() -> dict:
    inputs, records = load_inputs()
    omitted = {row["path"] for row in
               inputs["upstream"] + inputs["embedded_original_files"]}
    expected = {
        name[len(PAYLOAD_PREFIX):]: record for name, record in records.items()
        if name.startswith(PAYLOAD_PREFIX) and name not in omitted
    }
    if len(expected) != 709:
        raise VerificationError("Expected exactly 709 original files in Git")
    commit = subprocess.check_output(
        ["git", "rev-parse", f"refs/tags/{TAG}^{{commit}}"], text=True).strip()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise VerificationError("Release tag does not resolve to a Git commit")
    archive = subprocess.check_output(
        ["git", "archive", "--format=tar", commit, "--", PAPER_ROOT + "/"])
    observed = set()
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as tar:
        for member in tar:
            if member.isdir():
                continue
            if not member.isfile() or not member.name.startswith(PAPER_ROOT + "/"):
                raise VerificationError(f"Unexpected tagged entry: {member.name}")
            name = member.name[len(PAPER_ROOT) + 1:]
            if name in observed or name not in expected:
                raise VerificationError(f"Unexpected or duplicate tagged file: {name}")
            observed.add(name)
            record = expected[name]
            stream = tar.extractfile(member)
            if stream is None:
                raise VerificationError(f"Cannot read tagged file: {name}")
            data = stream.read()
            if len(data) != record["bytes"] or hashlib.sha256(data).hexdigest() != record["sha256"]:
                raise VerificationError(f"Tagged original changed: {name}")
    if observed != set(expected):
        raise VerificationError(f"Tag is missing {len(set(expected) - observed)} original files")
    return {
        "repository": REPOSITORY,
        "tag": TAG,
        "commit": commit,
        "verified_original_files": len(observed),
        "publication_manifest_sha256": inputs["publication_manifest_sha256"],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = verify_tag()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    log("release-tag-verified", **result)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError, VerificationError) as error:
        log("failed", error=str(error))
        sys.exit(1)
