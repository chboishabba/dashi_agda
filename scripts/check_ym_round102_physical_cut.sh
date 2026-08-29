#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

target="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound102Validation.agda"
test -f "$target"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round102}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"

files=(
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound102PhysicalCutExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound102Validation.agda
  DASHI/Physics/YangMills/BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact.agda
  DASHI/Physics/YangMills/BalabanA1HistoryUniformTwoSidedBetaRound102Exact.agda
  DASHI/Physics/YangMills/BalabanRowAShootingFixedPointTerminalExactRound102.agda
  DASHI/Physics/YangMills/BalabanCMP109116SameDifferentiatedCarrierRound102Exact.agda
  DASHI/Physics/YangMills/BalabanCMP116FirstGradientSharedMarkedExact.agda
  DASHI/Physics/YangMills/BalabanHeatDoobGradientCovarianceMarkedCauchyExact.agda
  DASHI/Physics/YangMills/BalabanCMP116GradientCovarianceToHeatDoobDebtExact.agda
  DASHI/Physics/YangMills/BalabanCMP116GradientCovarianceToWeightedHeatDoobExact.agda
  DASHI/Physics/YangMills/BalabanWeightedInfluenceEntryQuasiLocalExact.agda
  DASHI/Physics/YangMills/BalabanWeightedDysonQuasiLocalSeriesExact.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round102 physical-cut tranche contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'historyUniformTwoSidedBetaRound102Level = machineChecked' \
  DASHI/Physics/YangMills/BalabanA1HistoryUniformTwoSidedBetaRound102Exact.agda
grep -q 'shootingFixedPointTerminalCoordinateLevel = machineChecked' \
  DASHI/Physics/YangMills/BalabanRowAShootingFixedPointTerminalExactRound102.agda
grep -q 'sameDifferentiatedCarrierIdentityLevel = machineChecked' \
  DASHI/Physics/YangMills/BalabanCMP109116SameDifferentiatedCarrierRound102Exact.agda
grep -q 'temporalGradientCovarianceShellCompilerLevel = machineChecked' \
  DASHI/Physics/YangMills/BalabanHeatDoobGradientCovarianceMarkedCauchyExact.agda
grep -q 'weightedPositiveDysonSeriesCompilerLevel = machineChecked' \
  DASHI/Physics/YangMills/BalabanWeightedDysonQuasiLocalSeriesExact.agda
grep -q 'round102FrozenResearchCountStillFour' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound102PhysicalCutExact.agda

export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round102-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
scripts/run_agda29_parallel_check.sh "$target"
