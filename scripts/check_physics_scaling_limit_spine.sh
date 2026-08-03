#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

files=(
  DASHI/Physics/Units/MechanicalDimensionExact.agda
  DASHI/Physics/Units/PhysicalNormalizationExact.agda
  DASHI/Physics/Units/QuantumVacuumQuantityBridgeExact.agda
  DASHI/Physics/Limits/PhysicsLimitCommutingSquare.agda
  DASHI/Physics/Closure/NSTriadKNLuoScalingExact.agda
  DASHI/Physics/Closure/GRWeakFieldDimensionExact.agda
  DASHI/Physics/YangMills/BalabanClayT5MassScaleDimensionExact.agda
  DASHI/Physics/Closure/HEPDataCMSBelowZDrellYanClaimExact.agda
  DASHI/Unified/QuantumClassicalGravityBoundaryIntegration.agda
  DASHI/Physics/PhysicsScalingLimitSpineValidation.agda
)

for file in "${files[@]}"; do
  test -s "$file"
done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)' "${files[@]}"; then
  echo "postulate found in scaling/limit spine" >&2
  exit 1
fi

grep -q '10.1103/PhysRev.4.345' \
  DASHI/Physics/Units/MechanicalDimensionExact.agda
grep -q '10.1007/s00021-019-0411-z' \
  DASHI/Physics/Closure/NSTriadKNLuoScalingExact.agda
grep -q '10.1002/andp.19163540702' \
  DASHI/Physics/Closure/GRWeakFieldDimensionExact.agda
grep -q '10.1103/PhysRevLett.30.1343' \
  DASHI/Physics/YangMills/BalabanClayT5MassScaleDimensionExact.agda
grep -q '10.1140/epjc/s10052-023-11631-7' \
  DASHI/Physics/Closure/HEPDataCMSBelowZDrellYanClaimExact.agda

grep -q 'zeroFittedParametersProved = false' \
  DASHI/Physics/Closure/HEPDataCMSBelowZDrellYanClaimExact.agda
grep -q 'strictQuantumGravityTerminalProofSynthesized = false' \
  DASHI/Unified/QuantumClassicalGravityBoundaryIntegration.agda

check() {
  scripts/run_agda29_parallel_check.sh "$1"
}

for file in "${files[@]}"; do
  check "$file"
done
