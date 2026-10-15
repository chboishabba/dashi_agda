#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

files=(
  DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda
  DASHI/Physics/Foundations/ControlledPhysicalTransitionExact.agda
  DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterKernelValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterConsumersValidation.agda
  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringValidation.agda
  DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
  DASHI/Physics/Foundations/CausalTransportFTLValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
)

for file in "${files[@]}"; do
  test -f "$file" || { echo "missing required file: $file" >&2; exit 1; }
  if grep -nE '\{!!\}|(^|[[:space:]])postulate([[:space:]]|$)|--unsafe|allow-unsolved-metas' "$file"; then
    echo "forbidden hole, postulate, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'unresolvedChannelsAreNotZero' DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda
grep -q 'ResidualDirectAntigravityPermission' DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda
grep -q 'sameBodyForceFormDoesNotIdentifyMechanism' DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda
grep -q 'quantumInequalityAdmissible' DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
grep -q 'CausalSuperluminalTransportPromotion' DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
grep -q 'externalSourceDoesNotOwnDASHISynthesis' DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
grep -q 'moreGenericAbstractionCountsAsPhysicalClosure' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
