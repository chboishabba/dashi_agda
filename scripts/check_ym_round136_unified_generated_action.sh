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
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionA2HistoryRound137Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionA1HistoryRound138Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedGeneratedActionPhysicalHistoryRound139Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact.agda
  DASHI/Physics/YangMills/BalabanCombinedRGUnifiedActionRound141Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact.agda
  DASHI/Physics/YangMills/BalabanBC2FiniteLocalizedFirstVariationRound143Exact.agda
  DASHI/Physics/YangMills/BalabanCompositeStressFirstVariationRound144Exact.agda
  DASHI/Physics/YangMills/BalabanUnifiedPresentCutSchwingerRecoveryRound140Validation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round132-144 unified generated-action lane contains a hole, postulate, unsafe escape, or trust primitive" >&2
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
grep -q '^record UnifiedGeneratedActionA2History' "${files[5]}"
grep -q '^record UnifiedGeneratedActionA1History' "${files[6]}"
grep -q '^a1AndA2UseSamePhysicalCoupling :' "${files[7]}"
grep -q '^record UnifiedPresentCutSchwingerRecovery' "${files[8]}"
grep -q '^unifiedA2FullPrefixBelowOne :' "${files[8]}"
grep -q '^unifiedBC2SameDensityCalculus :' "${files[8]}"
grep -q '^unifiedContinuumFirstVariationIsLiteralStressPairing :' "${files[8]}"
grep -q '^record CompleteDensityEffectiveActionRealization' "${files[9]}"
grep -q '^asUnifiedGeneratedActionDensity :' "${files[9]}"
grep -q '^record FirstVariationLinearity' "${files[10]}"
grep -q '^cmp109FirstVariationIsFiniteLocalizedSum :' "${files[10]}"
grep -q '^record PresentCutBC2FirstVariationLinearity' "${files[11]}"
grep -q '^bc2GlobalFirstVariationIsFiniteLocalizedSum :' "${files[11]}"
grep -q '^record CompositeStressFirstVariationInputs' "${files[12]}"
grep -q '^compositeStressBuildsGlobalFirstVariation :' "${files[12]}"
grep -q 'round144CompositeStressD1Compiler' "${files[13]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round144}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round144-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanUnifiedPresentCutSchwingerRecoveryRound140Validation.agda
