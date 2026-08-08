#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_stage_euler_tree_complement_round2.sh

sources=(
  DASHI/Biology/NonaryCompletionPhaseQuotientExact.agda
  DASHI/Biology/SSP15ComplementPhaseProjectorExact.agda
  DASHI/Biology/OggPrimeNonaryAddressExact.agda
  DASHI/Biology/JCoarseFineEvaluationFibreExact.agda
  DASHI/Biology/SSP15NineObserverAtlasExact.agda
  DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
  DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
  DASHI/Biology/SSP15JCoarseFineIntegratedExact.agda
  DASHI/Biology/SSP15PrimeValuedStateExact.agda
  DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
  DASHI/Biology/PointedBulkSporadicTarotEverything.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source $source" >&2
    exit 1
  fi
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
  if grep -Pzo '\{!.*?!\}' "$source" >/dev/null; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'decodeAfterEncode'
  'complementFlipsBinaryPhase'
  'toAfterFromCoarseChannel'
  'ssp15InternalLaneCountIsFifteen'
  'laneProjectorOwnCoefficient'
  'laneProjectorReverseCovariant'
  'nonaryOggAddress'
  'nonThreeLaneModeIsPhaseMobile'
  'pointedSignedEdgeExact'
  'fortyOneIsHalfOfPointedEightyOneDivisionFree'
  'seventyOneRemovesCompleteBinaryFiveInterface'
  'canonicalJCoarseFineEvaluation'
  'jEvaluationIsSurjective'
  'fixedValueAssignmentFibreHasCardinalityThreePowerNineIsFalse'
  'ssp15NineAtlas'
  'transportEquivariant'
  'decompositionCertified'
  'pointedSignedCardinalityValue'
  'canonicalPrimeSpecificSSP15'
  'primeSpecificAddressReconstructsLane'
  'legacyUniformReadingContainsPrimeSpecificAddressIsFalse'
  'primeSpecificStageFiveSpectrum'
  'p2AndP71HaveDifferentFineRemainders'
  'everyPrimeSpecificSpectrumAddressReconstructs'
  'primeSpecificSSP15Reading'
  'sharedJEvaluationIsSurjective'
  'canonicalOggInternalLaneBijectionConstructedIsFalse'
  'PrimeValuedSSP15State'
  'p71A1Neutral'
  'p71A2Counterposed'
  'reversePrimeValuedPhaseInvolutive'
  'equalPrimeAndInternalCardinalitySuppliesCanonicalBijectionIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
