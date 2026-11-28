#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")" && pwd)"
rm -rf "$SRC/.lake"

WORK="${OSTQD_WORK_DIR:-$HOME/ostqd_lean4}"
mkdir -p "$WORK"
cp -f "$SRC/lean-toolchain" "$SRC/lakefile.toml" "$SRC/lake-manifest.json" "$SRC/OSTQD.lean" "$WORK/"
rm -rf "$WORK/OSTQD"
cp -r "$SRC/OSTQD" "$WORK/"
cd "$WORK"
sed -i 's/\r$//' OSTQD.lean OSTQD/*.lean lean-toolchain lakefile.toml lake-manifest.json

if [ ! -d "$WORK/.lake/packages/mathlib/.lake/build" ]; then
  lake exe cache get
fi

LOG="$SRC/VERIFICATION_LOG.txt"
{
  echo "================================================================================"
  echo "OSTQD — Lean 4 Kernel Build & Axiom Verification Log"
  echo "================================================================================"
  echo "Date (UTC): $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "Toolchain:  $(cat lean-toolchain)"
  echo "Lean:       $(lean --version)"
  echo "Lake:       $(lake --version)"
  echo ""
  echo "--- Step 1: lake build OSTQD ---"
} > "$LOG"

set +e
lake build OSTQD >> "$LOG" 2>&1
BUILD_RC=$?
echo "EXIT_CODE_BUILD=$BUILD_RC" >> "$LOG"
echo "" >> "$LOG"
if [ "$BUILD_RC" -ne 0 ]; then
  cat "$LOG"
  exit "$BUILD_RC"
fi

echo "--- Step 2: lake env lean OSTQD/AxiomCheck.lean (50 declarations) ---" >> "$LOG"
lake env lean OSTQD/AxiomCheck.lean >> "$LOG" 2>&1
AX_RC=$?
echo "EXIT_CODE_AXIOMCHECK=$AX_RC" >> "$LOG"
echo "" >> "$LOG"
if [ "$AX_RC" -ne 0 ]; then
  cat "$LOG"
  exit "$AX_RC"
fi
set -e

echo "--- Step 3: Static Forbidden-Token Audit (sorry / admit / axiom / constant / unsafe / sorryAx) ---" >> "$LOG"
if grep -rnE '(^|[^A-Za-z0-9_])(sorry|admit|axiom|constant|unsafe|sorryAx)([^A-Za-z0-9_]|$)' \
    OSTQD.lean OSTQD/Basic.lean OSTQD/Theorem*.lean; then
  echo "AUDIT_RESULT=FORBIDDEN_TOKEN_FOUND" >> "$LOG"
  exit 1
else
  echo "AUDIT_RESULT=ZERO_SORRY_OR_CUSTOM_AXIOM" >> "$LOG"
fi

echo "" >> "$LOG"
echo "--- Step 4: Declaration Count Check ---" >> "$LOG"
COUNT=$(grep -c '^#print axioms ' OSTQD/AxiomCheck.lean)
echo "AxiomCheck #print axioms count: $COUNT" >> "$LOG"

cat "$LOG"
