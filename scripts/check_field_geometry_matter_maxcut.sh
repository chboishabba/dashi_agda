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
  DASHI/Physics/CondensedMatter/MATBGBMFirstHarmonicC3Exact.agda
  DASHI/Physics/CondensedMatter/MATBGBMFirstHarmonicC3Validation.agda
  DASHI/Physics/CondensedMatter/MATBGBMEisensteinMatrixExact.agda
  DASHI/Physics/CondensedMatter/MATBGBMEisensteinMatrixValidation.agda
  DASHI/Physics/CondensedMatter/MATBGBMFirstShellReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGBMFirstShellReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGBMPlaneWaveReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGBMPlaneWaveReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGQuantumGeometryReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGQuantumGeometryReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGInteractingTHF2026SourceExact.agda
  DASHI/Physics/CondensedMatter/MATBGInteractingTHF2026SourceValidation.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Exact.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Validation.agda
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

for artifact in \
  scripts/matbg_bm_first_shell_replay.py \
  Docs/evidence/matbg_bm_first_shell_replay_2026-10-16.json \
  scripts/matbg_bm_plane_wave_replay.py \
  Docs/evidence/matbg_bm_plane_wave_replay_2026-10-16.json \
  scripts/matbg_bm_quantum_geometry.py \
  Docs/evidence/matbg_bm_quantum_geometry_2026-10-16.json; do
  test -f "$artifact" || { echo "missing execution artifact: $artifact" >&2; exit 1; }
done

grep -q 'unresolvedChannelsAreNotZero' DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda
grep -q 'ResidualDirectAntigravityPermission' DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda
grep -q 'sameBodyForceFormDoesNotIdentifyMechanism' DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda
grep -q 'qtmBestFitW0W1Hundredths' DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceExact.agda
grep -q 'tunnellingMatrixC3Covariance' DASHI/Physics/CondensedMatter/MATBGBMFirstHarmonicC3Exact.agda
grep -q 'qtmNormalizedTunnellingMatrix' DASHI/Physics/CondensedMatter/MATBGBMEisensteinMatrixExact.agda
grep -q 'firstShellNumericalExecutionPaid' DASHI/Physics/CondensedMatter/MATBGBMFirstShellReplayReceiptExact.agda
grep -q 'reciprocalLatticeExecutionPaid' DASHI/Physics/CondensedMatter/MATBGBMPlaneWaveReplayReceiptExact.agda
grep -q 'projectorGeometryExecutionPaid' DASHI/Physics/CondensedMatter/MATBGQuantumGeometryReplayReceiptExact.agda
grep -q 'xiao2026THFParameters' DASHI/Physics/CondensedMatter/MATBGInteractingTHF2026SourceExact.agda
grep -q 'highTemperatureMicrostates' DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Exact.agda
grep -q 'PhysicalGeneralizedCaloricWitness' DASHI/Physics/Foundations/GeneralizedCaloricCycleExact.agda
grep -q 'quantumInequalityAdmissible' DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
grep -q 'brownMaclay1969' DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda
grep -q 'PrecisionThrustClosureWitness' DASHI/Physics/Foundations/PrecisionThrustClosureExact.agda
grep -q 'CausalSuperluminalTransportPromotion' DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
grep -q 'externalSourceDoesNotOwnDASHISynthesis' DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
grep -q 'numericallyExecuted' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
grep -q 'numericalBMDoesNotBecomeExperiment' DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
