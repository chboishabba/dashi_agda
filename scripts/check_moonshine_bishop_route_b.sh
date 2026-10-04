#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_ARGS="${AGDA_ARGS:--i . -i DCHoTT-Agda -i vendor/bishop -i cubical -l standard-library}"

check_agda () {
  local file="$1"
  echo "==> checking ${file}"
  # shellcheck disable=SC2086
  "${AGDA_BIN}" ${AGDA_ARGS} "${file}"
}

check_agda DASHI/Foundations/BishopSineCosineSetoidCongruenceExact.agda
check_agda DASHI/Foundations/BishopConcreteTrigSeriesConvergenceExact.agda
check_agda DASHI/Analysis/BishopSetoidComplexExact.agda
check_agda DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda
check_agda DASHI/Moonshine/JInvariantEisensteinBishopSetoidFiniteQSeriesExact.agda
check_agda DASHI/Moonshine/JInvariantEisensteinBishopSetoidExtractionExact.agda
check_agda DASHI/Moonshine/BishopRound11MachinEisensteinRouteBExact.agda
check_agda DASHI/Interop/BishopRound11MachinBindingManifestExact.agda
check_agda DASHI/Interop/Round11MachinLeanBindingManifestExact.agda
check_agda DASHI/Interop/Round11MachinCrossProverRecognitionExact.agda
check_agda DASHI/Interop/LeanBishopCompletionCanonicalRouteReceiptExact.agda
check_agda DASHI/Moonshine/EisensteinBishopRouteBCurrentFrontierExact.agda
check_agda DASHI/Moonshine/EisensteinConvergenceEndgameCutsetExact.agda
check_agda DASHI/Moonshine/DeltaUnitCircleReflectionPhaseExact.agda
check_agda DASHI/Moonshine/JMDArchimedesDelta369FixedLocusBridgeExact.agda

grep -q 'normalizedDeltaEta24SameObjectPaidIsTrue'   DASHI/Moonshine/EisensteinBishopRouteBCurrentFrontierExact.agda

grep -q 'crossProverReplayProvenancePaidIsFalse'   DASHI/Moonshine/EisensteinBishopRouteBCurrentFrontierExact.agda

grep -q 'bishopQuotientEquivalentToLeanRealIsTrue'   DASHI/Interop/LeanBishopCompletionCanonicalRouteReceiptExact.agda

grep -q 'canonicalRound11MachinBindingInhabitedIsTrue'   DASHI/Interop/LeanBishopCompletionCanonicalRouteReceiptExact.agda

grep -q 'mappedRouteIndependentOfReplayBindingIsTrue'   DASHI/Interop/LeanBishopCompletionCanonicalRouteReceiptExact.agda

grep -q 'generatedAgdaReplayObservedIsFalse'   DASHI/Interop/LeanBishopCompletionCanonicalRouteReceiptExact.agda

grep -q 'actualCrossProverReplayObserved : Bool' \
  DASHI/Interop/Round11MachinCrossProverRecognitionExact.agda

grep -q 'actualAgdaRound11MachinBindingInLean : Bool' \
  DASHI/Moonshine/EisensteinConvergenceEndgameCutsetExact.agda

echo "Moonshine Bishop route-B focused checks passed."
