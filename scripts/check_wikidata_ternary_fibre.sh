#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Core/DependentRecoverableProjectionExact.agda
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
  DASHI/Ontology/DependentDefinitionFibreExact.agda
  DASHI/Ontology/WikidataTernaryFibreRegression.agda
  DASHI/Ontology/WikidataWorkingGroupRegression.agda
  DASHI/Ontology/WikidataWorkingGroupEverything.agda
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
require_pattern DASHI/Ontology/DependentDefinitionFibreExact.agda 'noToyotaFiestaSection'
require_pattern DASHI/Ontology/DependentDefinitionFibreExact.agda 'flatCountSplitsAsValidPlusInvalid'
require_pattern DASHI/Ontology/WikidataTernaryFibreRegression.agda 'threeBlockQuotientPlusResidualRoundTrips'

python3 scripts/benchmark_ternary_binary_locality.py >/dev/null

scripts/run_agda29_parallel_check.sh \
  DASHI/Ontology/WikidataTernaryFibreRegression.agda \
  DASHI/Ontology/WikidataWorkingGroupRegression.agda \
  DASHI/Ontology/WikidataWorkingGroupEverything.agda
