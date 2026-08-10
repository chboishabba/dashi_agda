#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_base369_relational_update_round8.sh

sources=(
  DASHI/Foundations/Base369SignedMembershipExact.agda
  DASHI/Foundations/Base369LayeredAttractorAndCoarseFineExact.agda
  DASHI/Foundations/Base369AddressSymmetryAndBranchGeometryExact.agda
  DASHI/Foundations/Base369ProcessBranchAttractorExact.agda
  DASHI/Foundations/Base369StepStateSymmetryQuotientExact.agda
  DASHI/Foundations/Base369WaveContinuousSymbolicCodingExact.agda
  DASHI/Foundations/Base369SymmetryWaveRound9Validation.agda
  DASHI/EverythingBase369SymmetryWaveRound9.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi

  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

required_markers=(
  'isGoodCollapsesInverseAndExterior'
  'attractiveDeadEnd369'
  'coarseFineCoordinateCountIs11'
  'sharedPrefixDepthSelf'
  'threeStrandBraidRelation'
  'propagatedSymmetryBrokenAtWitness'
  'beneficialBudgetExampleHasPositiveMargin'
  'serviceableButDirectionallyCancelled'
  'sameTritDifferentCostHasDiscrepancy'
  'refinedBranchesSplit'
  'decodeAfterEncode'
  'balancedNonarySymbolCount'
)

for marker in "${required_markers[@]}"; do
  if ! grep -Rqs --include='*.agda' "$marker" DASHI/Foundations; then
    echo "missing theorem marker: $marker" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Base369SymmetryWaveRound9Validation.agda \
  DASHI/EverythingBase369SymmetryWaveRound9.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
