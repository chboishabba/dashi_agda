#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"

required_files=(
  DASHI/Core/IntegrationConsumerDescentOrderExact.agda
  DASHI/Biology/IIT4FiniteCausalStructureExact.agda
  DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda
  DASHI/Biology/IIT4SystemPhiInputExact.agda
  DASHI/Biology/IIT4SymbolicScalarBackendExact.agda
  DASHI/Biology/IIT4FiniteExecutableKernelExact.agda
  DASHI/Biology/IIT4FiniteDistinctionExact.agda
  DASHI/Biology/IIT4FiniteRelationExact.agda
  DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda
  DASHI/Biology/IITXORGridAdversarialExact.agda
  DASHI/Biology/IITXORGridFibreCircuitBridgeExact.agda
  DASHI/Biology/IITXORGridFibreCalibrationExact.agda
  DASHI/Biology/IITMatchedFabricGateExperimentExact.agda
  DASHI/Biology/IIT369MatchedAlgebraControlExact.agda
  DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda
  DASHI/Biology/IITPointed27HyperformExperimentExact.agda
  DASHI/Biology/IITXOR369StressFamilyExact.agda
  DASHI/Biology/IITIIT4ConsumerDescentExact.agda
  DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda
  DASHI/Biology/IITCausalPantsFibreGluingExact.agda
  DASHI/Biology/IITCausalPantsOrientationBoundaryExact.agda
  DASHI/Biology/IIT369PantsGluingBridgeExact.agda
  DASHI/Biology/IITPointedTernary27FaceGluingExact.agda
  DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda
  DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda
  DASHI/Biology/IITPointedTernary27Origin26Exact.agda
  DASHI/Biology/IITPointedTernary27Recentered26Exact.agda
  DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda
  DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda
  DASHI/Biology/IITPhiIntegrationEverything.agda
  DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda
  DASHI/EverythingIITPhiIntegrationMaxCut.agda
  docs/superpowers/specs/2026-10-14-iit-hyperfabric-completion-design.md
  docs/superpowers/plans/2026-10-14-iit-hyperfabric-completion.md
  scripts/iit4_finite_reference.py
  scripts/check_iit4_finite_reference.py
  scripts/iit_xor_grid_calibration.py
  scripts/check_iit_xor_grid_calibration.py
  scripts/iit_matched_fabric_gate_sweep.py
  scripts/check_iit_matched_fabric_gate_sweep.py
  scripts/iit_369_algebra_scan.py
  scripts/check_iit_369_algebra_scan.py
  scripts/iit_hyperfabric_fixture_scan.py
  scripts/check_iit_hyperfabric_fixture_scan.py
  scripts/iit_pointed27_gluing_scan.py
  scripts/check_iit_pointed27_gluing_scan.py
  scripts/iit4_structure_reference.py
  scripts/check_iit4_structure_reference.py
  scripts/iit4_pyphi_oracle.py
  scripts/iit_xor_369_stress_scan.py
  scripts/check_iit_xor_369_stress_scan.py
  scripts/iit_consumer_descent_receipt.py
  scripts/check_iit_hyperfabric_completion.py
)

for path in "${required_files[@]}"; do
  [[ -f "$ROOT/$path" ]] || { echo "missing IIT completion file: $path" >&2; exit 1; }
done

require() { grep -Fq "$2" "$ROOT/$1" || { echo "missing contract '$2' in $1" >&2; exit 1; }; }
reject() { ! grep -Fq "$2" "$ROOT/$1" || { echo "forbidden contract '$2' in $1" >&2; exit 1; }; }

# Task 1: versioned executable system kernel.
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'data IIT4FormalismVersion'
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'iit4-2023'
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'iit4-2026'
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'record PositiveDenominatorFraction'
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'zeroDenominatorCannotInhabitPositiveFraction'
require DASHI/Biology/IIT4FiniteExecutableKernelExact.agda 'pythonReceiptIsNotKernelProof'
require scripts/iit4_finite_reference.py 'IIT_4_0_2023'
require scripts/iit4_finite_reference.py 'IIT_4_0_2026'
require scripts/iit4_finite_reference.py 'directional_partitions'
require scripts/iit4_finite_reference.py 'partitioned_effect_probability'
require scripts/iit4_finite_reference.py 'intrinsic_information'

# Task 2: XOR-grid calibration.
require DASHI/Biology/IITXORGridFibreCircuitBridgeExact.agda 'northWestNorthEastCircuit'
require DASHI/Biology/IITXORGridFibreCalibrationExact.agda 'currentXORGridCalibrationReceipt'
require DASHI/Biology/IITXORGridFibreCalibrationExact.agda 'graphCutStillNotPhi'
require scripts/iit_xor_grid_calibration.py 'grid2x2_step'
require scripts/check_iit_xor_grid_calibration.py 'distinct_phi_s'

# Task 3: matched H/mu sweeps.
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'record OutputInputGluing'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'sameFabricDifferentLocalAlgebraChangesOutput'
require DASHI/Biology/IITMatchedFabricGateExperimentExact.agda 'data FabricKind'
require DASHI/Biology/IITMatchedFabricGateExperimentExact.agda 'data GateKind'
require DASHI/Biology/IITMatchedFabricGateExperimentExact.agda 'fabricDoesNotDefinitionallyDeterminePhi'
require scripts/iit_matched_fabric_gate_sweep.py 'fixed_recurrent_fabric_vary_gate'
require scripts/iit_matched_fabric_gate_sweep.py 'fixed_binary_xor_vary_fabric'

# Task 4: exact same-cardinality 369 algebra control.
require DASHI/Biology/IIT369MatchedAlgebraControlExact.agda 'q9NonaryGroupIsomorphismImpossible'
require DASHI/Biology/IIT369MatchedAlgebraControlExact.agda 'phiProfileDoesNotIdentifyAlgebra'
require scripts/iit_369_algebra_scan.py 'z9_add'
require scripts/iit_369_algebra_scan.py 'f3_squared_add'
require scripts/iit_369_algebra_scan.py 'system_phi_profile_identifies_group_law'

# Task 5: path-indexed hyperfabric fixture semantics.
require DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda 'record IndexedCausalFabric'
require DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda 'causalGraphConnectionPartition'
require DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda 'partitionSemanticsRemainSeparate'
require scripts/iit_hyperfabric_fixture_scan.py 'global_section_partition'
require scripts/iit_hyperfabric_fixture_scan.py 'numeric_scan_currently_evaluates_causal_graph_partition_only'

# Task 6: pointed 27 / compatible gluing envelope.
require DASHI/Biology/IITPointed27HyperformExperimentExact.agda 'originPlusTwentySixRoundTrip'
require DASHI/Biology/IITPointed27HyperformExperimentExact.agda 'selectedCubiesStillDoNotDetermineTriadicFace'
require DASHI/Biology/IITPointed27HyperformExperimentExact.agda 'geometryDoesNotManufactureTPM'
require scripts/iit_pointed27_gluing_scan.py 'pairwise_face_overlaps'
require scripts/iit_pointed27_gluing_scan.py 'corner_face_triples'
require scripts/iit_pointed27_gluing_scan.py 'three_selected_cubie_choices'

# Task 7: distinctions, relations, CES and full-structure oracle adapter.
require DASHI/Biology/IIT4FiniteDistinctionExact.agda 'record FiniteDistinction'
require DASHI/Biology/IIT4FiniteDistinctionExact.agda 'systemPhiNotDistinctionPhi'
require DASHI/Biology/IIT4FiniteRelationExact.agda 'record FiniteRelation'
require DASHI/Biology/IIT4FiniteRelationExact.agda 'relationNeedsCongruentOverlap'
require DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda 'record FiniteCauseEffectStructure'
require DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda 'systemPhiIsNotBigPhi'
require scripts/iit4_structure_reference.py 'relation_phi_from_overlap'
require scripts/iit4_structure_reference.py 'big_phi'
require scripts/iit4_pyphi_oracle.py 'IIT_4_0_2023'
require scripts/iit4_pyphi_oracle.py 'sum_phi_distinctions'
require scripts/iit4_pyphi_oracle.py 'sum_phi_relations'

# Task 8: versioned XOR/369 stress family.
require DASHI/Biology/IITXOR369StressFamilyExact.agda 'record StressFamilyReceipt'
require DASHI/Biology/IITXOR369StressFamilyExact.agda 'stressRankingDoesNotSelfPromote'
require scripts/iit_xor_369_stress_scan.py 'system_phi_ranking_is_consciousness_ranking'

# Task 9: consumer descent.
require DASHI/Biology/IITIIT4ConsumerDescentExact.agda 'cardinalityLosesGroupLaw'
require DASHI/Biology/IITIIT4ConsumerDescentExact.agda 'cardinalityCannotFactorGroupLaw'
require DASHI/Biology/IITIIT4ConsumerDescentExact.agda 'selectedCubieObservationCannotRecoverTriadicFace'
require scripts/iit_consumer_descent_receipt.py 'consumer_factorization_must_be_paid_per_consumer'

# Task 10: completion ledger and verification provenance.
require DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda 'record CompletionLedger'
require DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda 'allTenSourceTasksPresent'
require DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda 'noFakeKernelPromotion'
require DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda 'noFakePyPhiExecutionClaim'
require scripts/check_iit_hyperfabric_completion.py 'source_complete_tasks'
require scripts/check_iit_hyperfabric_completion.py 'PENDING_EXTERNAL_AGDA_OR_CI_RECEIPT'

# Existing cross-domain firewalls remain live.
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'sameNineStatesDoNotForceSameAlgebra'
require DASHI/Biology/IITCausalPantsOrientationBoundaryExact.agda 'branchingDoesNotManufactureSynthesisOrientation'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'selectedCornerCocycle'
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'selectedCubiesDoNotDetermineTriadicFace'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recentringDoesNotManufactureGeometricSymmetry'
require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'vertexPartitionNotDefinitionallySectionPartition'
require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'integrationScoreDoesNotCreateBiologicalIdentity'

# Production aggregate remains acyclic; validation sits outside it.
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITHyperfabricCompletionReceiptExact'
reject DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPhiIntegrationMaxCutValidation'
require DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda 'import DASHI.Biology.IITPhiIntegrationEverything'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationEverything'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationMaxCutValidation'

echo 'IIT hyperfabric tasks 1-10 static contract: PASS'
