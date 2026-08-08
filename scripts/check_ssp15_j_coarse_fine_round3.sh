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

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

quotient=DASHI/Biology/NonaryCompletionPhaseQuotientExact.agda
internal=DASHI/Biology/SSP15ComplementPhaseProjectorExact.agda
address=DASHI/Biology/OggPrimeNonaryAddressExact.agda
jeval=DASHI/Biology/JCoarseFineEvaluationFibreExact.agda
atlas=DASHI/Biology/SSP15NineObserverAtlasExact.agda
bridge=DASHI/Biology/StageSymmetrySSP15BridgeExact.agda
spectrum=DASHI/Biology/StageSymmetrySSP15SpectrumExact.agda
integrated=DASHI/Biology/SSP15JCoarseFineIntegratedExact.agda
valued=DASHI/Biology/SSP15PrimeValuedStateExact.agda
validation=DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
aggregate=DASHI/Biology/PointedBulkSporadicTarotEverything.agda

require_pattern "$quotient" 'decodeAfterEncode'
require_pattern "$quotient" 'complementFlipsBinaryPhase'
require_pattern "$quotient" 'toAfterFromCoarseChannel'
require_pattern "$quotient" 'quotientDecodeAfterEncode'
require_pattern "$internal" 'ssp15InternalLaneCountIsFifteen'
require_pattern "$internal" 'laneProjectorOwnCoefficient'
require_pattern "$internal" 'laneProjectorReverseCovariant'
require_pattern "$address" 'nonaryOggAddress'
require_pattern "$address" 'toOggLaneNeverThree'
require_pattern "$address" 'nonThreeLaneModeIsPhaseMobile'
require_pattern "$address" 'pointedSignedEdgeExact'
require_pattern "$address" 'oggPrimeLaneCountIsFifteen'
require_pattern "$address" 'fortyOneIsHalfOfPointedEightyOneDivisionFree'
require_pattern "$address" 'seventyOneRemovesCompleteBinaryFiveInterface'
require_pattern "$jeval" 'canonicalJCoarseFineEvaluation'
require_pattern "$jeval" 'evaluateIsAtDistinguished'
require_pattern "$jeval" 'jEvaluationIsSurjective'
require_pattern "$jeval" 'ordinaryChannelIsNotCompletionJ'
require_pattern "$jeval" 'fixedValueAssignmentFibreHasCardinalityThreePowerNineIsFalse'
require_pattern "$atlas" 'ssp15NineAtlas'
require_pattern "$atlas" 'transportEquivariant'
require_pattern "$atlas" 'decompositionCertified'
require_pattern "$atlas" 'pointedSignedSizeFormula'
require_pattern "$bridge" 'canonicalPrimeSpecificSSP15'
require_pattern "$bridge" 'primeSpecificAddressReconstructsLane'
require_pattern "$bridge" 'legacyUniformReadingContainsPrimeSpecificAddressIsFalse'
require_pattern "$spectrum" 'primeSpecificStageFiveSpectrum'
require_pattern "$spectrum" 'p2AndP71HaveDifferentFineRemainders'
require_pattern "$spectrum" 'everyPrimeSpecificSpectrumAddressReconstructs'
require_pattern "$integrated" 'primeSpecificSSP15Reading'
require_pattern "$integrated" 'Scale.jCoarseFrequency'
require_pattern "$integrated" 'sharedJEvaluationIsSurjective'
require_pattern "$integrated" 'canonicalOggInternalLaneBijectionConstructedIsFalse'
require_pattern "$valued" 'PrimeValuedSSP15State'
require_pattern "$valued" 'p71A1Neutral'
require_pattern "$valued" 'p71A2Counterposed'
require_pattern "$valued" 'reversePrimeValuedPhaseInvolutive'
require_pattern "$valued" 'equalPrimeAndInternalCardinalitySuppliesCanonicalBijectionIsFalse'
require_pattern "$validation" 'pointedSignedChainReachesFortySeven'
require_pattern "$aggregate" 'import DASHI.Biology.SSP15PrimeValuedStateExact'

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/SSP15JCoarseFineRound3Validation.agda
