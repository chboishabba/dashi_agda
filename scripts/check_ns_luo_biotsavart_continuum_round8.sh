#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ns_luo_continuum_frontier_round7.sh

FILES=(
  DASHI/Physics/Closure/NSTriadKNFourierBiotSavartExact.agda
  DASHI/Physics/Closure/NSTriadKNMaxwellFluidBiotSavartBridgeExact.agda
  DASHI/Physics/Closure/NSTriadKNCorrectedFourierAngularStrainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoNearWindowCriticalGainExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFinitePeriodicHeatGradientTailExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoDyadicHaarRefinementExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoSmoothLPMomentScalingExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoParabolicCutoffTimeModulusExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoFiniteBKMTimeShellFubiniExact.agda
  DASHI/Physics/Closure/NSTriadKNWeakTypeVolumeStarvationNoGoExact.agda
  DASHI/Physics/Closure/NSTriadKNAirWaterTangentialStressAsymmetryExact.agda
  DASHI/Physics/Closure/NSTriadKNLuoBiotSavartContinuumRound8Validation.agda
)

for file in "${FILES[@]}"; do
  if grep -nE '\{!!\}|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--unsafe|=[[:space:]]*_[[:space:]]*$|\bdata[[:space:]]*(=|:|\)|→)' "$file"; then
    echo "forbidden hole, postulate, reserved binder, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/NSTriadKNLuoBiotSavartContinuumRound8Validation.agda
