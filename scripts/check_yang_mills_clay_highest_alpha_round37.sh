#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_yang_mills_clay_highest_alpha_round36.sh

sources=(
  DASHI/Physics/YangMills/BalabanSelectedPlaquetteLinearRepairModelExact.agda
  DASHI/Physics/YangMills/BalabanSelectedPlaquetteResidualBudgetRound37Exact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonGateSignatureRound37Exact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37RepairSelectorValidation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'selectedPlaquetteVariation'
  'selectedPlaquetteVariationGaugeAdmissible'
  'selectedPlaquetteVariationConstraintTangent'
  'selectedPlaquetteVariationExtractsSingleton'
  'selectedPlaquetteVariationChargeExact'
  'selectLinearPlaquetteVariation'
  'residualCoefficientLedgerExact'
  'selectedVariationSpilloverUpper'
  'covariantTransportAtom'
  'physicalCovariantPrefixTransportConstructedIsFalse'
  'GateISignature'
  'singletonIsLowerDegreeButOpen'
  'pairIsHigherDegreeButFiniteClosed'
  'oppositePairOrbitIsDistinguished'
  'physicalPrefixActionProvesTheseOrbitClassesIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound37RepairSelectorValidation.agda
