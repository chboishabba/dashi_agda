#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Physics/Closure/NSTriadKNRationalLerayProjectionExact.agda
  DASHI/Physics/Closure/NSTriadKNRationalLeraySelfAdjointExact.agda
  DASHI/Physics/Closure/NSTriadKNRationalLerayFiniteConvolutionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBernsteinExponentCalibrationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJensenSquareExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNormalizedWeightedJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePrefixJensenExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ11PrefixEnergyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedMeanValueSelectionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicHalfSplitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHalfShellPartitionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHalfShellEnergyPartitionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSourceFaithfulSection4Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedSourceSection4Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteIndexedSourceSection4Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteJ11HalfBudgetExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSourceJ11J12ProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedSourceJ11J12ProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteIndexedSourceJ1Exact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSchurEnvelopeRefinementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCanonicalSchurTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteSchurTailDominationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformCutoffEnergyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformEquation42SourceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformGronwallExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformGronwallProductExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteNonuniformGronwallVariationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteWeightedMeanValueGronwallExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSourceFaithfulRound4Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, unsolved-meta placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoSourceFaithfulRound4Validation.agda
