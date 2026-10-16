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
  DASHI/Physics/CondensedMatter/MATBG2026SourceDataAvailabilityExact.agda
  DASHI/Physics/CondensedMatter/MATBG2026SourceDataAvailabilityValidation.agda
  DASHI/Physics/CondensedMatter/MATBG2026PublicAcquisitionRouteExact.agda
  DASHI/Physics/CondensedMatter/MATBG2026PublicAcquisitionRouteValidation.agda
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
  DASHI/Physics/CondensedMatter/MATBGInteractingTHFLiteralMatricesExact.agda
  DASHI/Physics/CondensedMatter/MATBGInteractingTHFLiteralMatricesValidation.agda
  DASHI/Physics/CondensedMatter/MATBGTHFHubbardIAtomicReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGTHFHubbardIAtomicReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGTHFCoupledGreenReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGTHFCoupledGreenReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyQTMExact.agda
  DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyQTMValidation.agda
  DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyObstructionReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyObstructionValidation.agda
  DASHI/Physics/CondensedMatter/MATBGQTMMatrixElementObserverReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGQTMMatrixElementObserverValidation.agda
  DASHI/Physics/CondensedMatter/MATBGQTMElectrostaticsReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGQTMElectrostaticsReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Exact.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Validation.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorialReplayReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorialReplayValidation.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyMaxwellReplayContractExact.agda
  DASHI/Physics/CondensedMatter/MATBGEntropyMaxwellReplayContractValidation.agda
  DASHI/Physics/CondensedMatter/MATBGGeometryCaloricUpperBoundReceiptExact.agda
  DASHI/Physics/CondensedMatter/MATBGGeometryCaloricUpperBoundValidation.agda
  DASHI/Physics/Foundations/GeneralizedCaloricCycleExact.agda
  DASHI/Physics/Foundations/GeneralizedCaloricCycleValidation.agda
  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
  DASHI/Physics/Foundations/QuantumStressEnergyEngineeringValidation.agda
  DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda
  DASHI/Physics/Foundations/QuantumStressEnergySourceWeldValidation.agda
  DASHI/Physics/Foundations/CasimirGravityScalingReceiptExact.agda
  DASHI/Physics/Foundations/CasimirGravityScalingValidation.agda
  DASHI/Physics/Foundations/CasimirFiniteDiskGravityProxyReceiptExact.agda
  DASHI/Physics/Foundations/CasimirFiniteDiskGravityProxyValidation.agda
  DASHI/Physics/Foundations/PrecisionThrustClosureExact.agda
  DASHI/Physics/Foundations/PrecisionThrustClosureValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterExperimentParetoValidation.agda
  DASHI/Physics/Foundations/ScientistFrontierSiblingHandoffExact.agda
  DASHI/Physics/Foundations/ScientistFrontierSiblingHandoffValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterSiblingAuthorityHandoffExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterSiblingAuthorityHandoffValidation.agda
  DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
  DASHI/Physics/Foundations/CausalTransportFTLValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
  DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumValidation.agda
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
  Docs/evidence/matbg_bm_quantum_geometry_2026-10-16.json \
  scripts/matbg_qtm_matrix_element_observer.py \
  Docs/evidence/matbg_qtm_matrix_element_observer_2026-10-16.json \
  scripts/matbg_thf_hubbard_i_atomic_reference.py \
  Docs/evidence/matbg_thf_hubbard_i_atomic_reference_2026-10-16.json \
  scripts/matbg_thf_coupled_green_reference.py \
  Docs/evidence/matbg_thf_coupled_green_reference_2026-10-16.json \
  scripts/matbg_thf_self_consistency_obstruction.py \
  Docs/evidence/matbg_thf_self_consistency_obstruction_2026-10-16.json \
  scripts/matbg_entropy_combinatorial_replay.py \
  Docs/evidence/matbg_entropy_combinatorial_replay_2026-10-16.json \
  scripts/matbg_entropy_maxwell_replay_contract.py \
  Docs/evidence/matbg_entropy_maxwell_replay_contract_2026-10-16.json \
  scripts/matbg_geometry_caloric_upper_bound.py \
  Docs/evidence/matbg_geometry_caloric_upper_bound_2026-10-16.json \
  scripts/casimir_gravity_scaling.py \
  Docs/evidence/casimir_gravity_scaling_2026-10-16.json \
  scripts/casimir_finite_disk_gravity_proxy.py \
  Docs/evidence/casimir_finite_disk_gravity_proxy_2026-10-16.json \
  scripts/check_field_geometry_matter_evidence.py; do
  test -f "$artifact" || { echo "missing execution artifact: $artifact" >&2; exit 1; }
done

grep -q 'unresolvedChannelsAreNotZero' DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda
grep -q 'ResidualDirectAntigravityPermission' DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda
grep -q 'sameBodyForceFormDoesNotIdentifyMechanism' DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda
grep -q 'qtmBestFitW0W1Hundredths' DASHI/Physics/CondensedMatter/MATBG2026VerticalSliceExact.agda
grep -q 'publisherVisibleWorkbookCount' DASHI/Physics/CondensedMatter/MATBG2026SourceDataAvailabilityExact.agda
grep -q 'xiaoNIMSMDRRoute' DASHI/Physics/CondensedMatter/MATBG2026PublicAcquisitionRouteExact.agda
grep -q 'tunnellingMatrixC3Covariance' DASHI/Physics/CondensedMatter/MATBGBMFirstHarmonicC3Exact.agda
grep -q 'qtmNormalizedTunnellingMatrix' DASHI/Physics/CondensedMatter/MATBGBMEisensteinMatrixExact.agda
grep -q 'firstShellNumericalExecutionPaid' DASHI/Physics/CondensedMatter/MATBGBMFirstShellReplayReceiptExact.agda
grep -q 'reciprocalLatticeExecutionPaid' DASHI/Physics/CondensedMatter/MATBGBMPlaneWaveReplayReceiptExact.agda
grep -q 'projectorGeometryExecutionPaid' DASHI/Physics/CondensedMatter/MATBGQuantumGeometryReplayReceiptExact.agda
grep -q 'xiao2026THFParameters' DASHI/Physics/CondensedMatter/MATBGInteractingTHF2026SourceExact.agda
grep -q 'hcKPrime' DASHI/Physics/CondensedMatter/MATBGInteractingTHFLiteralMatricesExact.agda
grep -q 'atomicReferenceExecutionPaid' DASHI/Physics/CondensedMatter/MATBGTHFHubbardIAtomicReplayReceiptExact.agda
grep -q 'coupledGreenBlockExecutionPaid' DASHI/Physics/CondensedMatter/MATBGTHFCoupledGreenReplayReceiptExact.agda
grep -q 'selfConsistencyEquationsSourcePaid' DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyQTMExact.agda
grep -q 'unresolvedCutoffSensitivityExposed' DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyObstructionReceiptExact.agda
grep -q 'qtmElectrostaticsSourcePaid' DASHI/Physics/CondensedMatter/MATBGTHFSelfConsistencyQTMExact.agda
grep -q 'wavefunctionObserverExecutionPaid' DASHI/Physics/CondensedMatter/MATBGQTMMatrixElementObserverReceiptExact.agda
grep -q 'highTemperatureMicrostates' DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorics2026Exact.agda
grep -q 'combinatorialLogarithmReplayPaid' DASHI/Physics/CondensedMatter/MATBGEntropyCombinatorialReplayReceiptExact.agda
grep -q 'syntheticReplayNumericallyExecuted' DASHI/Physics/CondensedMatter/MATBGEntropyMaxwellReplayContractExact.agda
grep -q 'entropySwingExecutionPaid' DASHI/Physics/CondensedMatter/MATBGGeometryCaloricUpperBoundReceiptExact.agda
grep -q 'geometryCaloricUpperBoundNumericalReplay' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
grep -q 'PhysicalGeneralizedCaloricWitness' DASHI/Physics/Foundations/GeneralizedCaloricCycleExact.agda
grep -q 'quantumInequalityAdmissible' DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda
grep -q 'brownMaclay1969' DASHI/Physics/Foundations/QuantumStressEnergySourceWeldExact.agda
grep -q 'finiteDiskWeakFieldProxyPaid' DASHI/Physics/Foundations/CasimirFiniteDiskGravityProxyReceiptExact.agda
grep -q 'PrecisionThrustClosureWitness' DASHI/Physics/Foundations/PrecisionThrustClosureExact.agda
grep -q 'canonicalScientistFrontierSiblingReceipt' DASHI/Physics/Foundations/ScientistFrontierSiblingHandoffExact.agda
grep -q 'canonicalSiblingAuthorityHandoffBoundary' DASHI/Physics/Foundations/FieldGeometryMatterSiblingAuthorityHandoffExact.agda
grep -q 'CausalSuperluminalTransportPromotion' DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
grep -q 'metricClaimed' DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda
grep -q 'externalSourceDoesNotOwnDASHISynthesis' DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda
grep -q 'numericallyExecuted' DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda
grep -q 'qtmPublicAcquisitionRoutes' DASHI/Physics/Foundations/FieldGeometryMatterTerminalExecutionAddendumExact.agda
grep -q 'numericalBMDoesNotBecomeExperiment' DASHI/Physics/Foundations/FieldGeometryMatterTerminalValidation.agda

scripts/run_agda29_parallel_check.sh DASHI/Physics/Foundations/FieldGeometryMatterEverything.agda
