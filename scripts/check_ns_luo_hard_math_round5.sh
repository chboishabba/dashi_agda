#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteLiteralIncrementKernelFieldExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSmoothHardMultiplierFactorExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteProjectedShellEquation42Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePhysicalSection4BudgetDerivationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ12CommutatorDerivativeGainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ2HighHighGapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceWeightedJ11Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedCauchyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ1J2CombinationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ12FiveShellExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ11HalfRangeDerivedExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ12CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ2CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceJ1CriterionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceSection4NonlinearExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalWindowPropagationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoAlphaThreeHalvesFourShiftBootstrapExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFourResidueBlockDecayExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCanonicalSchurInfiniteCompletionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHardMathRound5Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, unsolved-meta placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoHardMathRound5Validation.agda
