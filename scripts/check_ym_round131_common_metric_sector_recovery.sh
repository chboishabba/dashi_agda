#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/BalabanDensityToLiteralFiniteMeasureRound124Exact.agda
  DASHI/Physics/YangMills/BalabanLiteralFiniteMeasureStressLaneRound125Exact.agda
  DASHI/Physics/YangMills/BalabanLiteralSchwingerStressRecoveryRound126Exact.agda
  DASHI/Physics/YangMills/BalabanOSLiteralSchwingerWeldRound127Exact.agda
  DASHI/Physics/YangMills/BalabanSameFamilyOSStressRecoveryRound128Exact.agda
  DASHI/Physics/YangMills/BalabanSectorQFTRecoveryExportRound129Exact.agda
  DASHI/Physics/YangMills/BalabanContinuumMetricStressPairingRound130Exact.agda
  DASHI/Physics/YangMills/BalabanCommonMetricSectorRecoveryRound131Exact.agda
  DASHI/Physics/YangMills/BalabanCommonMetricSectorRecoveryRound131Validation.agda
  DASHI/Physics/YangMills/BalabanDensityAnchoredStressLaneRound123Exact.agda
  DASHI/Physics/YangMills/YangMillsClayLiteralTopDownConstructionExact.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round124-131 sector recovery contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record BalabanDensityLiteralFiniteMeasureWeld' "${files[0]}"
grep -q '^record LiteralBalabanSchwingerStressRecovery' "${files[2]}"
grep -q '^record SameFamilyOSStressRecovery' "${files[4]}"
grep -q '^record BalabanSectorQFTRecoveryExport' "${files[5]}"
grep -q '^literalStressDerivativeRecovery :' "${files[5]}"
grep -q '^record ContinuumMetricStressPairingWeld' "${files[6]}"
grep -q '^completedStressFunctionalEqualsCanonicalStressPairing :' "${files[6]}"
grep -q '^record CommonMetricReadyBalabanSectorRecovery' "${files[7]}"
grep -q '^continuumSectorFirstVariationIsLiteralStressPairing :' "${files[7]}"
grep -q '^literalFiniteFamilyContinuumRecovery :' "${files[7]}"
grep -q '^literalSchwingerFamilyRecovery :' "${files[7]}"
grep -q 'round131CommonMetricSectorCompiler' "${files[8]}"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round131}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round131-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanCommonMetricSectorRecoveryRound131Validation.agda
