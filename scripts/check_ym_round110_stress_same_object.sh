#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

r109="DASHI/Physics/YangMills/BalabanSameFamilyStressCauchySchwingerRound109Exact.agda"
r110="DASHI/Physics/YangMills/BalabanStressSameObjectProvenanceRound110Exact.agda"
r111="DASHI/Physics/YangMills/BalabanMarkedStressLiteralDerivativeRound111Exact.agda"
r112="DASHI/Physics/YangMills/BalabanStressShellEnergyToHilbertRound112Exact.agda"
r113="DASHI/Physics/YangMills/BalabanStressShellPartitionEnergyRound113Exact.agda"
r114="DASHI/Physics/YangMills/BalabanLiteralStressCoordinateRound114Exact.agda"
r115="DASHI/Physics/YangMills/BalabanLiteralStressCompletionRound115Exact.agda"
validation="DASHI/Physics/YangMills/BalabanLiteralStressCompletionRound115Validation.agda"

files=(
  "$r109" "$r110" "$r111" "$r112" "$r113" "$r114" "$r115" "$validation"
  DASHI/Physics/YangMills/BalabanCMP119CompatibleLocalExpectationFlowExact.agda
  DASHI/Physics/YangMills/BalabanTopDownSummableRGIncrementExact.agda
  DASHI/Physics/YangMills/BalabanRowBActivityEntropyToShellEnergyExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceGeometricShellEnergyExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceNuclearCompositeFieldExact.agda
  DASHI/Physics/YangMills/BalabanMarkedSourceCompositeStressFieldExact.agda
  DASHI/Physics/YangMills/YangMillsClayLiteralTopDownConstructionExact.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round110-115 stress completion contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^record LiteralStressSameObjectProvenance' "$r110"
grep -q '^completedCMP119StressIsLiteralClayStressDerivative :' "$r110"
grep -q 'cauchyCompletionIsActualMarkedStressFunctional' "$r110"
grep -q '^completedMarkedStressFunctionalIsLiteralClayStressDerivative :' "$r111"
grep -q '^record LiteralStressCoefficientShellIdentification' "$r112"
grep -q '^stressCoefficientEnergyUniformBound :' "$r112"
grep -q '^record LiteralStressShellPartition' "$r113"
grep -q '^coefficientPrefixEnergyIsShellPrefix :' "$r113"
grep -q '^record LiteralStressCoordinate' "$r114"
grep -q '^asSameObjectProvenance :' "$r114"
grep -q '^record CompiledLiteralStressCompletion' "$r115"
grep -q '^compiledStressCompletionIsLiteralClayStressDerivative :' "$r115"
grep -q 'round115CompletionCompiler' "$validation"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round115}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round115-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh "$validation"
