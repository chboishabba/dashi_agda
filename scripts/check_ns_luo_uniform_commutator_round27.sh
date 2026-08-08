#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_galerkin_critical_ledger_round26.sh

sources=(
  DASHI/Physics/Closure/NSTriadKNLuoUniformCommutatorTaxRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyContinuationRound27Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoUniformCommutatorRound27Validation.agda
)

for source in "${sources[@]}"; do
  test -s "$source"
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|allow-unsolved-metas|TERMINATING|NO_POSITIVITY_CHECK|{-# OPTIONS --unsafe|\{![^}]*!\}' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
done

required_patterns=(
  'cutoffIndependentCommutatorCellCoefficient'
  'finiteCutoffIndependentCommutatorTax'
  'halfDoubleScalePair'
  'quarterFourScalePair'
  'energyIdentityConstructsBoundWitness'
  'energyControlledFiniteContinuation'
  'repositoryRealPicardLindelofInstantiatedIsFalse'
)

for pattern in "${required_patterns[@]}"; do
  grep -R -F "$pattern" "${sources[@]}" >/dev/null
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoUniformCommutatorRound27Validation.agda
