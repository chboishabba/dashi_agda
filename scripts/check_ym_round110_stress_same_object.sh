#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

r109="DASHI/Physics/YangMills/BalabanSameFamilyStressCauchySchwingerRound109Exact.agda"
r110="DASHI/Physics/YangMills/BalabanStressSameObjectProvenanceRound110Exact.agda"
validation="DASHI/Physics/YangMills/BalabanStressSameObjectProvenanceRound110Validation.agda"

files=(
  "$r109"
  "$r110"
  "$validation"
  DASHI/Physics/YangMills/BalabanCMP119CompatibleLocalExpectationFlowExact.agda
  DASHI/Physics/YangMills/BalabanTopDownSummableRGIncrementExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceNuclearCompositeFieldExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceCompositeStressFieldExact.agda
  DASHI/Physics/YangMills/YangMillsClayLiteralTopDownConstructionExact.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round110 stress same-object provenance contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record LiteralStressSameObjectProvenance' "$r110"
grep -q '^stressDifferenceCauchyModulus :' "$r110"
grep -q '^completedCMP119StressIsLiteralClayStressPairing :' "$r110"
grep -q 'literalCMP119StressCompletionProvenanceLevel : ProofLevel' "$r110"
grep -q '^record SourceNativeStressScaleCauchy' "$r109"
grep -q '^record LiteralSchwingerStressMarkedCompletion' "$r109"
grep -q 'round110SameObjectCompilerIsMachineChecked' "$validation"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round110}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round110-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh "$validation"
