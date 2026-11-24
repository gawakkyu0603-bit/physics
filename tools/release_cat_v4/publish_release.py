#!/usr/bin/env python3
"""Add verified assets only to the existing, fixed CAT v4 GitHub Release.

Run only in the manually dispatched workflow. Authentication is provided by the
workflow's built-in GITHUB_TOKEN through GH_TOKEN. This never creates a release,
changes a tag, replaces an asset, or reads browser credentials.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from build_release import VerificationError, load_inputs, log, verify
from verify_tag import REPOSITORY, TAG


def gh_json(endpoint: str) -> dict:
    result = subprocess.run(["gh", "api", endpoint], check=True,
                            capture_output=True, text=True)
    return json.loads(result.stdout)


def current_tag_commit() -> str:
    ref = gh_json(f"repos/{REPOSITORY}/git/ref/tags/{TAG}")["object"]
    for _ in range(5):
        if ref["type"] == "commit":
            return ref["sha"]
        if ref["type"] != "tag":
            break
        ref = gh_json(f"repos/{REPOSITORY}/git/tags/{ref['sha']}")["object"]
    raise VerificationError("Remote tag does not resolve to a commit")


def release() -> dict:
    value = gh_json(f"repos/{REPOSITORY}/releases/tags/{TAG}")
    if value.get("tag_name") != TAG or value.get("draft") is not False:
        raise VerificationError("Expected the existing published CAT v4 release")
    return value


def verify_remote_asset(asset: dict, expected: dict) -> None:
    if asset.get("state") != "uploaded" or asset.get("size") != expected["bytes"]:
        raise VerificationError(f"Existing asset has wrong state or size: {expected['name']}")
    remote_hash = asset.get("digest")
    if remote_hash:
        if remote_hash != "sha256:" + expected["sha256"]:
            raise VerificationError(f"Existing asset has a different hash: {expected['name']}")
        return
    # Some older assets lack a server digest. Verify their actual public bytes.
    with tempfile.TemporaryDirectory(prefix="cat-existing-asset-") as directory:
        subprocess.run([
            "gh", "release", "download", TAG, "--repo", REPOSITORY,
            "--pattern", expected["name"], "--dir", directory,
        ], check=True)
        verify(Path(directory) / expected["name"], expected)


def asset_index(value: dict) -> dict[str, dict]:
    assets = value.get("assets", [])
    indexed = {asset["name"]: asset for asset in assets}
    if len(indexed) != len(assets):
        raise VerificationError("Release has duplicate asset names")
    return indexed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assets", type=Path, required=True)
    parser.add_argument("--tag-verification", type=Path, required=True)
    args = parser.parse_args()
    if os.environ.get("GITHUB_REPOSITORY") != REPOSITORY:
        raise VerificationError("This recipe is restricted to its original public repository")
    if os.environ.get("GITHUB_EVENT_NAME") != "workflow_dispatch":
        raise VerificationError("Only an explicit manual workflow dispatch can publish")
    inputs, _ = load_inputs()
    verified_tag = json.loads(args.tag_verification.read_text(encoding="utf-8"))
    if (verified_tag.get("repository") != REPOSITORY or verified_tag.get("tag") != TAG
            or verified_tag.get("verified_original_files") != 709
            or verified_tag.get("publication_manifest_sha256") != inputs["publication_manifest_sha256"]):
        raise VerificationError("Missing or inconsistent frozen-original tag verification")
    if current_tag_commit() != verified_tag["commit"]:
        raise VerificationError("The release tag changed after original-file verification")
    expected = inputs["assets"]
    if len(expected) != 5:
        raise VerificationError("Expected exactly five frozen assets")
    for row in expected:
        verify(args.assets / row["name"], row)
    existing = asset_index(release())
    missing = []
    for row in expected:
        if row["name"] in existing:
            verify_remote_asset(existing[row["name"]], row)
            log("existing-release-asset-verified", name=row["name"])
        else:
            missing.append(str(args.assets / row["name"]))
    if missing:
        # Deliberately omit --clobber: concurrent or changed assets must fail.
        subprocess.run(["gh", "release", "upload", TAG, "--repo", REPOSITORY,
                        *missing], check=True)
    final = asset_index(release())
    for row in expected:
        if row["name"] not in final:
            raise VerificationError(f"Release asset is still missing: {row['name']}")
        verify_remote_asset(final[row["name"]], row)
    if current_tag_commit() != verified_tag["commit"]:
        raise VerificationError("The release tag changed during publication")
    url = f"https://github.com/{REPOSITORY}/releases/tag/{TAG}"
    log("release-assets-verified", assets=5, newly_uploaded=len(missing), url=url)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as stream:
            stream.write(f"## CAT v4 release verified\n\nAll five frozen assets match their expected SHA256 hashes.\n\n[Open the release]({url})\n")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError, VerificationError) as error:
        log("failed", error=str(error))
        sys.exit(1)
