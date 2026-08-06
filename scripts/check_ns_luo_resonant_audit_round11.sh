#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_terminal_interaction_round10.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNCherevanResonantSourceAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanScaleCovarianceNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanTwoIndexHighHighLowExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanPacketScaleAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanWindowScaleNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanSchurYoungLaneAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanPeriodicCutoffAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanFiniteConvolutionSupportLossExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanFiniteOrthogonalityAuditExact.agda
  DASHI/Physics/Closure/NSTriadKNCherevanWideNarrowAssemblyExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoEnergyInterpolationDeficitExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoCriticalTerminalScaleExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCriticalShellFunctionalExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteHighHighLowBernsteinGainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCriticalInteractionKernelExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteCriticalFourClassClosureExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoResonantAuditRound11Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoResonantAuditRound11Validation.agda
