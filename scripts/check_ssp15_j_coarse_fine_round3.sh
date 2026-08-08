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
  DASHI/Biology/SSP15JCoarseFineIntegratedExact.agda
  DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
  DASHI/Biology/PointedBulkSporadicTarotEverything.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
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
  'pointedSignedCardinalityValue'
  'canonicalPrimeSpecificSSP15'
  'primeSpecificAddressReconstructsLane'
  'legacyUniformReadingContainsPrimeSpecificAddressIsFalse'
  'primeSpecificSSP15Reading'
  'canonicalOggInternalLaneBijectionConstructedIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
