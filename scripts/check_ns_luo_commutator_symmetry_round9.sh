#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_biotsavart_continuum_round8.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTransportCommutatorIdentityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTransportCommutatorMomentBoundExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePairedCommutatorSecondOrderExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePairedCommutatorSecondMomentBoundExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCommutatorScaleAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTriadMultiplierDifferenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteParityMatchedNonlinearityExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEightParityReconstructionExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoLerayLaplacianCommutationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalDissipationTailClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoNearWindowCommutatorDissipationClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBiotSavartLerayFactorisationExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCommutatorSymmetryRound9Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoCommutatorSymmetryRound9Validation.agda
