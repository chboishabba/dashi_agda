#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

target="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound103SourceCoordinateWeldExact.agda"

files=(
  "$target"
  DASHI/Physics/YangMills/BalabanA1Equation51FiveChannelSameObjectRound103Exact.agda
  DASHI/Physics/YangMills/BalabanA2LiteralSameHistoryPrefixSensitivityRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109116FiniteEffectiveActionHessianRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109116SourceContinuationRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109Equation51LocalizedHessianRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP116SubstitutedActivityHessianRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109116ConventionTransportRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP116CommonAnalyticRadiusRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact.agda
  DASHI/Physics/YangMills/BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact.agda
  DASHI/Physics/YangMills/BalabanHeatDoobSameDensityLogHessianRound103Exact.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round103 source-coordinate weld contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'round103FrozenResearchCountStillFour' "$target"
grep -q 'a1Equation51FiveChannelSameObjectCompilerLevel' DASHI/Physics/YangMills/BalabanA1Equation51FiveChannelSameObjectRound103Exact.agda
grep -q 'a2ShellToCumulativeSensitivityLevel' DASHI/Physics/YangMills/BalabanA2LiteralSameHistoryPrefixSensitivityRound103Exact.agda
grep -q 'physicalHessianSplitsIntrinsicPlusSubstitution' DASHI/Physics/YangMills/BalabanCMP116SubstitutedActivityHessianRound103Exact.agda
grep -q 'polarizationIsLocalizedCompositeHessianSum' DASHI/Physics/YangMills/BalabanCMP109Equation51LocalizedHessianRound103Exact.agda
grep -q 'cmp109PolarizationIsCMP116PhysicalMarkedHessian' DASHI/Physics/YangMills/BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact.agda
grep -q 'covarianceDefinition' DASHI/Physics/YangMills/BalabanHeatDoobSameDensityLogHessianRound103Exact.agda
grep -q 'heatDoobHessianIsStaticMinusCovariance' DASHI/Physics/YangMills/BalabanHeatDoobSameDensityLogHessianRound103Exact.agda

# Regression against receipt-shuffling in the strict new seams.
! grep -q 'sameBlockingScaleConvention : Set' DASHI/Physics/YangMills/BalabanCMP109116SourceContinuationRound103Exact.agda
! grep -q 'cutoffVolumeScaleUniform : Set' DASHI/Physics/YangMills/BalabanCMP116CommonAnalyticRadiusRound103Exact.agda
! grep -q 'heatInitialPotentialIsCarrierPotential : Set' DASHI/Physics/YangMills/BalabanHeatDoobSameDensityLogHessianRound103Exact.agda
! grep -q 'physicalHessianUsesCommonRadius : Scale' DASHI/Physics/YangMills/BalabanCMP116PhysicalCompositeHessianMarkedShellRound103Exact.agda

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round103}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round103-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh "$target"
