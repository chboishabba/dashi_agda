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

  DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceExact.agda
  DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceValidation.agda
  DASHI/Physics/Foundations/GeneralizedCaloricCycleExact.agda
  DASHI/Physics/Foundations/GeneralizedCaloricCycleValidation.agda

  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringValidation.agda
  DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda
  DASHI/Physics/Foundations/QuantumStressEnergySourceWeldValidation.agda

  DASHI/Physics/Foundations/PrecisionThrustClosureExact.agda
  DASHI/Physics/Foundations/PrecisionThrustClosureValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoValidation.agda

  DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
  DASHI/Physics/Foundations/CausalTransportFTLValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
)

for file in "${files[@]}"; do
  test -f "$file" || { echo "missing required file: $file" >&2; exit 1; }
  if grep -nE '\{!!\}|(^|[[:space:]])postulate([[:space:]]|$)|--unsafe|allow-unsolved-metas|--type-in-type|--no-positivity-check|--no-termination-check' "$file"; then
    echo "forbidden hole, postulate, unsolved-meta or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q 'unresolvedChannelsAreNotZero' DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda
grep -q 'ResidualDirectAntigravityPermission' DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda
grep -q 'sameBodyForceFormDoesNotIdentifyMechanism' DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda

grep -q 'timeReversalConjugatesCandidateValleyPhase' DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceExact.agda
grep -q 'sameSampleQTMEntropyPaid' DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceExact.agda
grep -q 'PhysicalGeneralizedCaloricWitness' DASHI/Physics/Foundations/GeneralizedCaloricCycleExact.agda

grep -q 'quantumInequalityAdmissible' DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
grep -q 'brownMaclay1969' DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda
grep -q 'sameObjectRenormalizedStressMeasured' DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda

grep -q 'PrecisionThrustClosureWitness' DASHI/Physics/Foundations/PrecisionThrustClosureExact.agda
grep -q 'precisionThrustIndependentReplication' DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoExact.agda
grep -q 'externalPaymentCannotBeReplacedByMoreFormalism' DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoExact.agda

grep -q 'CausalSuperluminalTransportPromotion' DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
grep -q 'externalSourceDoesNotOwnDASHISynthesis' DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
grep -q 'sourcePaid' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
grep -q 'sameMaterialClassCountsAsSameSample' DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda

grep -q 'moreGenericAbstractionCountsAsPhysicalClosure' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
grep -q 'monolithicFoundationsEverythingIntegration' DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
