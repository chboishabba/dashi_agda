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
r116="DASHI/Physics/YangMills/BalabanNormalizedStressInsertionRound116Exact.agda"
r117="DASHI/Physics/YangMills/BalabanLiteralStressCoordinateSourceWeldRound117Exact.agda"
r118="DASHI/Physics/YangMills/BalabanCanonicalMetricToCMP119StressRound118Exact.agda"
r119="DASHI/Physics/YangMills/BalabanCanonicalMetricSelectedStressRound119Exact.agda"
r120="DASHI/Physics/YangMills/BalabanCanonicalMetricStressLaneRound120Exact.agda"
validation115="DASHI/Physics/YangMills/BalabanLiteralStressCompletionRound115Validation.agda"
validation120="DASHI/Physics/YangMills/BalabanCanonicalMetricStressLaneRound120Validation.agda"

files=(
  "$r109" "$r110" "$r111" "$r112" "$r113" "$r114" "$r115"
  "$r116" "$r117" "$r118" "$r119" "$r120"
  "$validation115" "$validation120"
  DASHI/Physics/YangMills/BalabanNormalizedExpectationCrossNumeratorExact.agda
  DASHI/Physics/YangMills/BalabanCMP116CanonicalMetricSourceDomainRound106Exact.agda
  DASHI/Physics/YangMills/BalabanCMP116CanonicalMetricStressRepresentationRound106Exact.agda
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
  echo "Round109-120 canonical metric stress lane contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q '^completedCMP119StressIsLiteralClayStressDerivative :' "$r110"
grep -q '^completedMarkedStressFunctionalIsLiteralClayStressDerivative :' "$r111"
grep -q '^coefficientPrefixEnergyIsShellPrefix :' "$r113"
grep -q '^record LiteralStressCoordinate' "$r114"
grep -q '^record CompiledLiteralStressCompletion' "$r115"
grep -q '^record MetricStressNormalizedInsertionWeld' "$r116"
grep -q 'stressInsertion : Source.SourceNativeOrdinaryCharacteristicPair source' "$r116"
grep -q '^record LiteralStressCoordinateSourceWeld' "$r117"
grep -q '^record CanonicalMetricCMP119StressWeld' "$r118"
grep -q '^finiteCanonicalMetricVariationIsCMP119StressInsertion :' "$r118"
grep -q '^record CanonicalMetricSelectedStressWeld' "$r119"
grep -q '^canonicalMetricVariationIsExactSelectedCMP119StressInsertion :' "$r119"
grep -q '^record CanonicalMetricLiteralStressLane' "$r120"
grep -q '^finiteMetricVariationIsSelectedCMP119Insertion :' "$r120"
grep -q '^selectedStressCompletionIsLiteralClayStressDerivative :' "$r120"
grep -q 'round120FullMetricStressLaneCompiler' "$validation120"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round120}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/ym-round120-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh "$validation120"
scripts/run_agda29_parallel_check.sh "$validation115"
