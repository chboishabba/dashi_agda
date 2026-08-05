#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_commutator_symmetry_round9.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNMisurSecondCommutationSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteBonyFourClassAccountingExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTerminalInteractionAmplitudeNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighLowDyadicGainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteTerminalTailVanishingExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoHomogeneousTerminalWindowClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteEnergyBernsteinWindowNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoTerminalInteractionRound10Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoTerminalInteractionRound10Validation.agda
