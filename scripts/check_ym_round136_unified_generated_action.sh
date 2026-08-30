#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionDensityRound132Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionFirstVariationRound133Exact.agda
  DASHI/Physics/YangMills/BalabanPresentCutCanonicalMetricDomainRound134Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionStressScaleRound135Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionRecoveryRound136Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionRecoveryRound136Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round132-136 unified generated-action lane contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record UnifiedGeneratedActionDensity' "${files[0]}"
grep -q '^selectedDensityRepresentsExactBC1Potential :' "${files[0]}"
grep -q '^record UnifiedGeneratedActionFirstVariation' "${files[1]}"
grep -q '^sameActionFirstVariation :' "${files[1]}"
grep -q '^record PresentCutMetricSpecificInputs' "${files[2]}"
grep -q '^presentCutDomainUsesExactBC1Radius :' "${files[2]}"
grep -q '^record UnifiedGeneratedActionStressScale' "${files[3]}"
grep -q '^stressSelectedDensityIndexIsUnifiedActionIndex :' "${files[3]}"
grep -q '^record UnifiedGeneratedActionSectorRecovery' "${files[4]}"
grep -q '^continuumFirstVariationOfUnifiedGeneratedActionIsLiteralStressPairing :' "${files[4]}"
grep -q 'round136UnifiedRecoveryCompiler' "${files[5]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round136}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round136-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionRecoveryRound136Validation.agda
