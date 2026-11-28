#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")" && pwd)"
rm -rf "$SRC/.lake"

WORK="$HOME/.cache/ostqd_layer2_build"
mkdir -p "$WORK"
cp -f "$SRC/lean-toolchain" "$SRC/lakefile.toml" "$SRC/lake-manifest.json" "$SRC/OSTQD_Layer2.lean" "$WORK/"
rm -rf "$WORK/OSTQD_Layer2"
cp -r "$SRC/OSTQD_Layer2" "$WORK/"
cd "$WORK"
sed -i 's/\r$//' OSTQD_Layer2.lean OSTQD_Layer2/*.lean lean-toolchain lakefile.toml lake-manifest.json

LOG="$SRC/VERIFICATION_LOG.txt"
{
  echo "=== LEAN VERSION ==="
  lean --version
  echo "=== FORBIDDEN TOKEN SCAN ==="
  if grep -rnE '(^|[^A-Za-z0-9_])(sorry|admit|axiom|constant|unsafe|sorryAx)([^A-Za-z0-9_]|$)' \
      OSTQD_Layer2.lean OSTQD_Layer2/Basic.lean OSTQD_Layer2/Theorem*.lean OSTQD_Layer2/Proposition*.lean; then
    echo "FORBIDDEN TOKENS FOUND!"
    exit 1
  else
    echo "ZERO FORBIDDEN TOKENS FOUND."
  fi
} > "$LOG"

if [ ! -d "$WORK/.lake/packages/mathlib/.lake/build" ]; then
  lake exe cache get >/dev/null 2>&1 || lake exe cache get
fi

echo "=== LAKE BUILD ===" >> "$LOG"
lake build OSTQD_Layer2 >> "$LOG" 2>&1

echo "=== AXIOM CHECK ===" >> "$LOG"
lake env lean OSTQD_Layer2/AxiomCheck.lean >> "$LOG" 2>&1

cat "$LOG"
