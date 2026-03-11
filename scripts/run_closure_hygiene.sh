#!/usr/bin/env bash
set -u -o pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

TS="$(date +%Y%m%d_%H%M%S)"
OUT_DIR="${1:-artifacts/closure_hygiene_${TS}}"
mkdir -p "$OUT_DIR"

AGDA_BIN="${AGDA_BIN:-agda}"

STATUS=0

run_step() {
  local name="$1"
  shift
  local log="$OUT_DIR/${name}.log"
  echo "[run] $name"
  echo "[cmd] $*" > "$log"
  echo "---" >> "$log"
  if "$@" >> "$log" 2>&1; then
    echo "[ok]  $name"
  else
    local rc=$?
    echo "[fail] $name (exit $rc)"
    STATUS=1
  fi
}

# 1) Top-level compile gates (the real finish line).
run_step 01_canonical_stagec_build \
  "$AGDA_BIN" -i . DASHI/Physics/Closure/CanonicalStageCTheoremBundle.agda

run_step 02_everything_build \
  "$AGDA_BIN" -i . DASHI/Everything.agda

# 2) Canonical-path audit (imports + potential drift markers).
{
  echo "# Canonical Path Audit"
  echo
  echo "## Canonical bridge imports (expected)"
  rg -n "import DASHI\\.Physics\\.Closure\\.(ContractionForcesQuadraticTheorem|ContractionQuadraticToSignatureBridgeTheorem|QuadraticToCliffordBridgeTheorem|CanonicalContractionToCliffordBridgeTheorem|PhysicsUnification|CanonicalStageCTheoremBundle)" DASHI || true
  echo
  echo "## Potential alternate-route imports inside closure stack (review)"
  rg -n "import DASHI\\.Geometry\\.(QuadraticEmergence|QuadraticFromNorm|QuadraticFromParallelogram|QuadraticFormEmergence)|import DASHI\\.Physics\\.ContractionQuadraticBridge" DASHI/Physics/Closure || true
} > "$OUT_DIR/03_canonical_path_audit.txt"

# 3) Placeholder/postulate audit outside core path.
{
  echo "# Placeholder/Postulate Audit"
  echo
  echo "## postulate declarations"
  rg -n "^[[:space:]]*postulate\\b" DASHI || true
  echo
  echo "## placeholder markers"
  rg -n "placeholder|to be discharged|TODO" DASHI || true
} > "$OUT_DIR/04_placeholder_postulate_audit.txt"

# 4) Quick canonical closure status pointers.
{
  echo "# Closure Status Pointers"
  rg -n "module DASHI\\.Physics\\.Closure\\.(PhysicsUnification|CanonicalContractionToCliffordBridgeTheorem|CanonicalStageCTheoremBundle|PhysicsClosureFullShift)" DASHI/Physics/Closure -S || true
} > "$OUT_DIR/05_closure_status_pointers.txt"

cat > "$OUT_DIR/SUMMARY.txt" <<EOF_SUM
Closure hygiene run: $TS
Root: $ROOT_DIR
Agda binary: $AGDA_BIN

Build checks:
  - CanonicalStageCTheoremBundle: $(if [ -f "$OUT_DIR/01_canonical_stagec_build.log" ] && ! grep -q "\[fail\]" "$OUT_DIR/01_canonical_stagec_build.log" 2>/dev/null; then echo "see log"; else echo "see log"; fi)
  - Everything.agda: see log

Artifacts:
  - $OUT_DIR/01_canonical_stagec_build.log
  - $OUT_DIR/02_everything_build.log
  - $OUT_DIR/03_canonical_path_audit.txt
  - $OUT_DIR/04_placeholder_postulate_audit.txt
  - $OUT_DIR/05_closure_status_pointers.txt

Overall status: $(if [ "$STATUS" -eq 0 ]; then echo "PASS"; else echo "FAIL"; fi)
EOF_SUM

if [ "$STATUS" -eq 0 ]; then
  echo "[done] PASS. Artifacts in $OUT_DIR"
else
  echo "[done] FAIL. Artifacts in $OUT_DIR"
fi

exit "$STATUS"
