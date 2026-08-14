#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_physical_development_round20.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Biology/Physical/PersistentCarrierTemplatingExact.agda
  DASHI/Biology/Physical/CrossCarrierTemplatingFamilyExact.agda
  DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda
  DASHI/Biology/Physical/DynamicTissueGraphRewriteExact.agda
  DASHI/Biology/Physical/DynamicTopologyFutureDefectExact.agda
  DASHI/Biology/Physical/HierarchicalGoalConstraintCompilerExact.agda
  DASHI/Biology/Physical/GoalErrorDescentControllerExact.agda
  DASHI/Biology/Physical/GraphGeneratingGoalControllerExact.agda
  DASHI/Biology/Physical/DevelopmentalMeasurementQuotientExact.agda
  DASHI/Biology/Physical/CoupledDevelopmentalOperatorStackExact.agda
  DASHI/Biology/Physical/ContextDependentPadicPhysicalMapExact.agda
  DASHI/Biology/Physical/MultiscaleSelfBoundaryExact.agda
  DASHI/Biology/Physical/DNAHelixDihedralExact.agda
  DASHI/Biology/Physical/DNASequenceHelixPositionExact.agda
  DASHI/Biology/Physical/DNAHelixTernaryQuantizationResidualExact.agda
  DASHI/Biology/Physical/DNAChemistryRegulatoryOperatorBridgeExact.agda
  DASHI/Biology/Physical/C3CubeFourier27Exact.agda
  DASHI/Biology/Physical/MorphogeneticControlFieldCapacityExact.agda
  DASHI/Biology/Physical/IteratedAttractorScaleLiftExact.agda
  DASHI/EverythingDynamicBiologyRound21.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q 'prionTemplatingDoesNotPromoteAgency' DASHI/Biology/Physical/PersistentCarrierTemplatingExact.agda
grep -q 'sameGenomeDoesNotReconstructPersistentCarrier' DASHI/Biology/Physical/PersistentCarrierTemplatingExact.agda
grep -q 'prionConformationTemplatesNormal' DASHI/Biology/Physical/CrossCarrierTemplatingFamilyExact.agda
grep -q 'morphologicalTargetCanBeReimposed' DASHI/Biology/Physical/CrossCarrierTemplatingFamilyExact.agda
grep -q 'drivenPersistenceDoesNotForceReplication' DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda
grep -q 'replicationAndVariationDoNotForceAgency' DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda
grep -q 'twoStepFastOutnumbersSlow' DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda

grep -q 'divisionChangesVertexCarrier' DASHI/Biology/Physical/DynamicTissueGraphRewriteExact.agda
grep -q 'connectionChangesEdgeCarrier' DASHI/Biology/Physical/DynamicTissueGraphRewriteExact.agda
grep -q 'repairHitsIntegratedConstraint' DASHI/Biology/Physical/DynamicTissueGraphRewriteExact.agda
grep -q 'morphologyWithoutTopologyIsNotFutureSafe' DASHI/Biology/Physical/DynamicTopologyFutureDefectExact.agda

grep -q 'leftHandHasDistinctTissueRefinements' DASHI/Biology/Physical/HierarchicalGoalConstraintCompilerExact.agda
grep -q 'digitFieldHasDistinctCellPolicies' DASHI/Biology/Physical/HierarchicalGoalConstraintCompilerExact.agda
grep -q 'positiveDefectStrictlyDecreases' DASHI/Biology/Physical/GoalErrorDescentControllerExact.agda
grep -q 'severeRecovers' DASHI/Biology/Physical/GoalErrorDescentControllerExact.agda
grep -q 'closedLoopFactorises' DASHI/Biology/Physical/GraphGeneratingGoalControllerExact.agda
grep -q 'closedLoopHitsIntegratedConstraint' DASHI/Biology/Physical/GraphGeneratingGoalControllerExact.agda
grep -q 'closedLoopFixesIntegratedState' DASHI/Biology/Physical/GraphGeneratingGoalControllerExact.agda

grep -q 'phenotypeOnlyNotFutureSafe' DASHI/Biology/Physical/DevelopmentalMeasurementQuotientExact.agda
grep -q 'canonicalSameMeasuredDifferentHidden' DASHI/Biology/Physical/DevelopmentalMeasurementQuotientExact.agda
grep -q 'independentCoordinateWritesCommute' DASHI/Biology/Physical/CoupledDevelopmentalOperatorStackExact.agda
grep -q 'transcriptionAndTranslationDoNotCommute' DASHI/Biology/Physical/CoupledDevelopmentalOperatorStackExact.agda
grep -q 'bioelectricAndMechanicalDoNotCommute' DASHI/Biology/Physical/CoupledDevelopmentalOperatorStackExact.agda

grep -q 'sameFineAddressDifferentContextChangesParameter' DASHI/Biology/Physical/ContextDependentPadicPhysicalMapExact.agda
grep -q 'shapeAloneDoesNotDetermineOurHand' DASHI/Biology/Physical/MultiscaleSelfBoundaryExact.agda

grep -q 'dihedralConjugation' DASHI/Biology/Physical/DNAHelixDihedralExact.agda
grep -q 'pairedSiteInvolutive' DASHI/Biology/Physical/DNAHelixDihedralExact.agda
grep -q 'uvComplementReflection' DASHI/Biology/Physical/DNAHelixDihedralExact.agda
grep -q 'positionAdvanceCommutesWithPhaseRotation' DASHI/Biology/Physical/DNASequenceHelixPositionExact.agda
grep -q 'embeddingCommutesWithAdvance' DASHI/Biology/Physical/DNASequenceHelixPositionExact.agda
grep -q 'reopenQuantizedPhaseExactly' DASHI/Biology/Physical/DNAHelixTernaryQuantizationResidualExact.agda
grep -q 'p2p3CollapseToSameTrit' DASHI/Biology/Physical/DNAHelixTernaryQuantizationResidualExact.agda
grep -q 'decodeEncodeExact' DASHI/Biology/Physical/DNAHelixTernaryQuantizationResidualExact.agda

grep -q 'atEnergyIsZero' DASHI/Biology/Physical/DNAChemistryRegulatoryOperatorBridgeExact.agda
grep -q 'gcEnergyIsTwo' DASHI/Biology/Physical/DNAChemistryRegulatoryOperatorBridgeExact.agda
grep -q 'sameDNAEnergyDifferentContextChangesCellParameter' DASHI/Biology/Physical/DNAChemistryRegulatoryOperatorBridgeExact.agda

grep -q 'cubeCharacterHomomorphism' DASHI/Biology/Physical/C3CubeFourier27Exact.agda
grep -q 'cubeRoundTrip' DASHI/Biology/Physical/C3CubeFourier27Exact.agda
grep -q 'cellRoundTrip' DASHI/Biology/Physical/C3CubeFourier27Exact.agda

grep -q 'decodeEncodeExact' DASHI/Biology/Physical/MorphogeneticControlFieldCapacityExact.agda
grep -q 'targetConstraintRoundTrip' DASHI/Biology/Physical/MorphogeneticControlFieldCapacityExact.agda
grep -q 'junctionResidualRestoresExactTarget' DASHI/Biology/Physical/MorphogeneticControlFieldCapacityExact.agda
grep -q 'multiscaleRepairReachesIntegratedOrgan' DASHI/Biology/Physical/IteratedAttractorScaleLiftExact.agda

grep -q '10.1126/science.6801762' DASHI/Biology/Physical/PersistentCarrierTemplatingExact.agda
grep -q '10.1038/171737a0' DASHI/Biology/Physical/DNAHelixDihedralExact.agda
grep -q '10.4103/1673-5374.165216' DASHI/Biology/Physical/GoalErrorDescentControllerExact.agda
grep -q '10.1016/j.biosystems.2017.08.009' DASHI/Biology/Physical/HierarchicalGoalConstraintCompilerExact.agda
grep -q '10.1007/s00018-023-04790-z' DASHI/Biology/Physical/MultiscaleSelfBoundaryExact.agda
grep -q '10.1063/1.4818538' DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda
grep -q '10.1103/PhysRevE.100.022414' DASHI/Biology/Physical/AbiogenesisInevitabilityBoundaryExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingDynamicBiologyRound21.agda
else
  echo "agda unavailable: structural/fail-closed round-21 scan completed; no kernel-clean claim"
fi
