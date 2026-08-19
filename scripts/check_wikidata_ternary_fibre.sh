#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Core/ConsumerDescentMinimalObserverExact.agda
  DASHI/Core/ContextIndexedObservationFibrationExact.agda
  DASHI/Core/ContextIndexedObservationFibrationRegression.agda
  DASHI/Core/ResidualSymmetryCollisionFibreExact.agda
  DASHI/Core/ResidualSymmetryCollisionFibreRegression.agda
  DASHI/Core/TopDownObservationCalculusExact.agda
  DASHI/Core/DependentRecoverableProjectionExact.agda
  DASHI/EverythingTopDownObservationCalculus.agda
  DASHI/Foundations/TernaryNativeMinimalityExact.agda
  DASHI/Foundations/BalancedTernaryAntipodalOrbitExact.agda
  DASHI/Foundations/BalancedTernaryAntipodalResidualCodecExact.agda
  DASHI/Foundations/BalancedTernaryDependentRecoverableBridgeExact.agda
  DASHI/Foundations/BalancedTernaryNineZeroFibreCountExact.agda
  DASHI/Foundations/Base369InteractionAntipodalFibreExact.agda
  DASHI/Foundations/Base369InteractionObserverJoinExact.agda
  DASHI/Foundations/Base369NineCoordinateAggregateBridgeExact.agda
  DASHI/Foundations/TernaryNineAntipodalD4SeparationExact.agda
  DASHI/Algebra/BalancedTernaryOppositionEvidenceBridgeExact.agda
  DASHI/Cognition/PNF/BinaryBalancedTernaryAggregateLossExact.agda
  DASHI/Interop/PointedSignAntipodal369SeparationExact.agda
  DASHI/Ontology/DependentDefinitionFibreExact.agda
  DASHI/Ontology/WikidataTernaryFibreRegression.agda
  DASHI/Ontology/WikidataWorkingGroupRegression.agda
  DASHI/Ontology/WikidataWorkingGroupEverything.agda
  DASHI/Ontology/WikidataWorkingGroupFullProvenanceEverything.agda
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
    echo "missing required theorem marker '$pattern' in $source" >&2
    exit 1
  fi
}

require_pattern DASHI/Core/ConsumerDescentMinimalObserverExact.agda 'sectionedDescentIffFibreConstant'
require_pattern DASHI/Core/ConsumerDescentMinimalObserverExact.agda 'sectionedDescentIffConsumerSufficient'
require_pattern DASHI/Core/ConsumerDescentMinimalObserverExact.agda 'canonicalConsumerObserverIsLeast'
require_pattern DASHI/Core/ConsumerDescentMinimalObserverExact.agda 'explicitDescentReusesFactorizedRefinement'
require_pattern DASHI/Core/ContextIndexedObservationFibrationExact.agda 'splitLiftFactorizationEquation'
require_pattern DASHI/Core/ContextIndexedObservationFibrationExact.agda 'splitLiftFactorizationArrow'
require_pattern DASHI/Core/ContextIndexedObservationFibrationExact.agda 'observationCommutesWithSplitLift'
require_pattern DASHI/Core/ContextIndexedObservationFibrationExact.agda 'fullBenabouCartesianUniquenessConstructed'
require_pattern DASHI/Core/ContextIndexedObservationFibrationRegression.agda 'situatedObservationIsNotAdequate'
require_pattern DASHI/Core/ContextIndexedObservationFibrationRegression.agda 'situatedIdentityCompositeFactorsThroughLift'
require_pattern DASHI/Core/ResidualSymmetryCollisionFibreExact.agda 'symmetryMoveCreatesObserverCollision'
require_pattern DASHI/Core/ResidualSymmetryCollisionFibreExact.agda 'sectorPairStrictlyRefinesCoarse'
require_pattern DASHI/Core/ResidualSymmetryCollisionFibreRegression.agda 'antipodeMoveGeneratesCoarseCollision'
require_pattern DASHI/Core/ResidualSymmetryCollisionFibreRegression.agda 'signRefinesAntipodalPoleClass'
require_pattern DASHI/Core/TopDownObservationCalculusExact.agda 'dependentCodeIsAdequateForEveryConsumer'
require_pattern DASHI/Core/TopDownObservationCalculusExact.agda 'toyObserverIsNotReconstructive'
require_pattern DASHI/Core/DependentRecoverableProjectionExact.agda 'dependentCodeSeparating'
require_pattern DASHI/Foundations/TernaryNativeMinimalityExact.agda 'noOneBitInjection'
require_pattern DASHI/Foundations/TernaryNativeMinimalityExact.agda 'noExactPositiveOnlyReconstruction'
require_pattern DASHI/Foundations/TernaryNativeMinimalityExact.agda 'binarySimulationPreservesAntipode'
require_pattern DASHI/Foundations/BalancedTernaryAntipodalOrbitExact.agda 'antipodalClass27CountIsFourteen'
require_pattern DASHI/Foundations/Base369InteractionAntipodalFibreExact.agda 'blockOrientationClassCountIs2744'
require_pattern DASHI/Foundations/Base369InteractionAntipodalFibreExact.agda 'allThreeNoncentralOrientationFibreSizeIsEight'
require_pattern DASHI/Foundations/BalancedTernaryAntipodalResidualCodecExact.agda 'decodeAfterEncodeRound'
require_pattern DASHI/Foundations/BalancedTernaryAntipodalResidualCodecExact.agda 'encodeAfterDecodeRound'
require_pattern DASHI/Foundations/BalancedTernaryDependentRecoverableBridgeExact.agda 'canonicalDependentCodeSeparatesFineCarrier'
require_pattern DASHI/Foundations/BalancedTernaryNineZeroFibreCountExact.agda 'aggregateZeroFibreCountIs3139'
require_pattern DASHI/Interop/PointedSignAntipodal369SeparationExact.agda 'pointedFiveModeSignSizeIsEleven'
require_pattern DASHI/Ontology/DependentDefinitionFibreExact.agda 'noToyotaFiestaSection'
require_pattern DASHI/Ontology/DependentDefinitionFibreExact.agda 'flatCountSplitsAsValidPlusInvalid'
require_pattern DASHI/Ontology/WikidataTernaryFibreRegression.agda 'positiveOnlyCannotBeSufficientForSignedIdentity'
require_pattern DASHI/Ontology/WikidataTernaryFibreRegression.agda 'antipodalDependentCodeSufficientForFineIdentity'
require_pattern DASHI/Ontology/WikidataTernaryFibreRegression.agda 'threeBlockQuotientPlusResidualRoundTrips'

python3 scripts/benchmark_ternary_binary_locality.py >/dev/null

scripts/run_agda29_parallel_check.sh \
  DASHI/Core/ContextIndexedObservationFibrationRegression.agda \
  DASHI/Core/ResidualSymmetryCollisionFibreRegression.agda \
  DASHI/EverythingTopDownObservationCalculus.agda \
  DASHI/Ontology/WikidataTernaryFibreRegression.agda \
  DASHI/Ontology/WikidataWorkingGroupRegression.agda \
  DASHI/Ontology/WikidataWorkingGroupEverything.agda \
  DASHI/Ontology/WikidataWorkingGroupFullProvenanceEverything.agda
