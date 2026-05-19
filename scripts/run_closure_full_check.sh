#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

AGDA_BIN="${AGDA_BIN:-agda}"
TIMEOUT_SECS="${TIMEOUT_SECS:-0}"
OUT_DIR="${OUT_DIR:-artifacts/closure_full_check_$(date +%Y%m%d_%H%M%S)}"
CHUNK="closure-full"

usage() {
  cat <<'EOF'
Usage: scripts/run_closure_full_check.sh [--chunk NAME] [OUT_DIR]

Runs a deliberate offline closure-certification pass and captures full logs.

Chunks:
  transport-observable
  dynamics-gauge
  known-limits
  atomic-gap
  closure-full

Environment:
  AGDA_BIN       agda binary to use (default: agda)
  TIMEOUT_SECS   optional timeout in seconds; 0 means no timeout
  OUT_DIR        output directory for logs and status

Outcomes:
  clean
  error
  too_large
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --chunk)
      shift
      [ "$#" -gt 0 ] || { echo "[error] missing value for --chunk" >&2; exit 2; }
      CHUNK="$1"
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      if [ "${OUT_DIR_SET:-0}" -eq 0 ]; then
        OUT_DIR="$1"
        OUT_DIR_SET=1
      else
        echo "[error] unexpected argument: $1" >&2
        exit 2
      fi
      ;;
  esac
  shift
done

declare -a TARGETS=()
case "$CHUNK" in
  transport-observable)
    TARGETS=(
      "DASHI/Physics/Closure/ShiftContractObservableTransportPrimeCompatibilityProfileInstance.agda"
      "DASHI/Physics/Closure/ShiftObservableSignaturePressureConsumer.agda"
    )
    ;;
  dynamics-gauge)
    TARGETS=(
      "DASHI/Physics/DashiDynamicsShiftInstance.agda"
      "DASHI/Physics/Closure/CanonicalAbstractGaugeMatterInstance.agda"
    )
    ;;
  known-limits)
    TARGETS=(
      "DASHI/Physics/Closure/CanonicalGaugeMatterStrengtheningTheorem.agda"
      "DASHI/Physics/Closure/KnownLimitsFullMatterGaugeTheorem.agda"
    )
    ;;
  atomic-gap)
    TARGETS=(
      "DASHI/Physics/Closure/AtomicPhotonuclearContactGateTheorem.agda"
      "DASHI/Physics/Closure/CanonicalScheduleIndependentNaturalChargeNextIngredientGap.agda"
    )
    ;;
  closure-full)
    TARGETS=(
      "DASHI/Physics/Closure/PhysicsClosureValidationSummary.agda"
    )
    ;;
  *)
    echo "[error] unknown chunk: $CHUNK" >&2
    usage >&2
    exit 2
    ;;
esac

mkdir -p "$OUT_DIR"
LOG_FILE="$OUT_DIR/${CHUNK}.log"
STATUS_FILE="$OUT_DIR/${CHUNK}.status"
META_FILE="$OUT_DIR/${CHUNK}.meta"

{
  echo "chunk=$CHUNK"
  echo "agda_bin=$AGDA_BIN"
  echo "timeout_secs=$TIMEOUT_SECS"
  printf 'targets='
  printf '%s ' "${TARGETS[@]}"
  echo
  echo "started_at=$(date --iso-8601=seconds)"
} > "$META_FILE"

run_one() {
  local target="$1"
  echo "==> $target"
  if [ "$TIMEOUT_SECS" -gt 0 ]; then
    timeout "$TIMEOUT_SECS" "$AGDA_BIN" -i . -l standard-library "$target"
  else
    "$AGDA_BIN" -i . -l standard-library "$target"
  fi
}

set +e
{
  for target in "${TARGETS[@]}"; do
    run_one "$target"
  done
} >"$LOG_FILE" 2>&1
RC=$?
set -e

STATUS="clean"
if [ "$RC" -eq 124 ]; then
  STATUS="too_large"
elif [ "$RC" -ne 0 ]; then
  STATUS="error"
fi

{
  echo "status=$STATUS"
  echo "rc=$RC"
  echo "finished_at=$(date --iso-8601=seconds)"
  echo "log=$LOG_FILE"
} > "$STATUS_FILE"

echo "$STATUS"
echo "log: $LOG_FILE"
echo "status: $STATUS_FILE"

if [ "$STATUS" = "clean" ]; then
  exit 0
fi
if [ "$STATUS" = "too_large" ]; then
  exit 124
fi
exit "$RC"
