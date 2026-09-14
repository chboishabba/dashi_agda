#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/ExperimentalCoordinateDesignExact.agda
  DASHI/Core/ExperimentalCoordinateProjectionBridgeExact.agda
  DASHI/Core/ExperimentalCoordinateProjectionBridgeRegression.agda
  DASHI/Core/ConsumerFibreRepairExact.agda
  DASHI/Core/FactorisationSpineCrosswalkExact.agda
  DASHI/Core/FactorisationSpineCrosswalkRegression.agda
  DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
  DASHI/Interop/FactorisationSpineCrossDomainAdapterRegression.agda
  DASHI/Core/ActionabilityCostedExperimentChoiceExact.agda
  DASHI/Core/CommonExperimentRealisationExact.agda
  DASHI/Core/DiscriminatorSynthesisExact.agda
  DASHI/Core/CoarseFineRelativeFibreExact.agda
  DASHI/Core/CandidateFamilyExecutionExact.agda
  DASHI/Core/CandidateFamilyExecutionRegression.agda
  DASHI/Core/RequirementConflictBatchExecutionExact.agda
  DASHI/Core/RequirementConflictBatchExecutionRegression.agda
  DASHI/Core/RelativeFineModelFidelityOrthogonalityExact.agda
  DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda
  DASHI/Core/ConsumerAdequacyJointPolicyBidiCompilerExact.agda
  DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
  DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
  DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
  DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
  DASHI/Core/ConsumerReductionJointPolicyBridgeExact.agda
  DASHI/Core/JointSequentialInformationFidelityFixtureExact.agda
  DASHI/Core/SequentialExperimentPlanningValidation.agda
  DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda
  DASHI/ComputerScience/RSA260RequirementConflictBatchSpineExact.agda
  DASHI/ComputerScience/RSA260RequirementConflictBatchSpineRegression.agda
  DASHI/ComputerScience/FlyCandidateFamilyExecutionAdapterExact.agda
  DASHI/ComputerScience/FlyCandidateFamilyExecutionAdapterRegression.agda
  DASHI/CoarseFineFabricEverything.agda
  DASHI/Physics/Foundations/GRQFTDiscriminatorSynthesisExact.agda
  DASHI/Physics/Foundations/GRQFTSequentialExperimentPlannerExact.agda
  DASHI/Environment/LESDiscriminatorSynthesisExact.agda
  DASHI/Environment/LESSequentialExperimentPlannerExact.agda
  DASHI/Environment/LESJointSequentialMeasurementFidelityPolicyExact.agda
  DASHI/Environment/LESProofDerivedDecisionAdequacyExact.agda
  DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required sequential experiment source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^fromProvenanceBearingQuotient :' DASHI/Core/CoarseFineRelativeFibreExact.agda
grep -q '^coarseProjectionRetainsRelativeFineResidual :' DASHI/Core/CoarseFineRelativeFibreExact.agda
grep -q '^fineSensitivityRefutesCoarseOnlyReduction :' DASHI/Core/CoarseFineRelativeFibreExact.agda
grep -q 'fineMeansOnlyHigherComputeCostIsFalse' DASHI/Core/CoarseFineRelativeFibreExact.agda
grep -q '^relativeFineEvidenceMove :' DASHI/Core/RelativeFineModelFidelityOrthogonalityExact.agda
grep -q '^modelChangeKeepsWorldCoordinates :' DASHI/Core/RelativeFineModelFidelityOrthogonalityExact.agda
grep -q 'relativeFineInformationEqualsModelFidelityIsFalse' DASHI/Core/RelativeFineModelFidelityOrthogonalityExact.agda
grep -q 'relativeFineCanBeDisclosedAsEvidenceAtFixedModelIsTrue' DASHI/Core/RelativeFineModelFidelityOrthogonalityExact.agda

grep -q '^coordinateSeparationYieldsProjectionCollision :' DASHI/Core/ExperimentalCoordinateProjectionBridgeExact.agda
grep -q '^coordinateReadCannotFactorThroughExisting :' DASHI/Core/ExperimentalCoordinateProjectionBridgeExact.agda
grep -q '^refinementRepairSeparatesWitness :' DASHI/Core/ConsumerFibreRepairExact.agda
grep -q '^queryFactorsToNonFactor :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^nonFactorToFactorized :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^projectionCollisionToNonFactorability :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^projectionCollisionToNonDescent :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^projectionCollisionBlocksFactorizedRefinement :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^projectionCollisionRepairRequiresSeparation :' DASHI/Core/FactorisationSpineCrosswalkExact.agda
grep -q '^actionCrossingProjectionCollision :' DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
grep -q '^securityRoutingProjectionCollision :' DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
grep -q '^indigenousPropositionProvenanceCollision :' DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
grep -q '^securityRoutingRepairRequiresSeparation :' DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
grep -q '^indigenousProvenanceRepairRequiresSeparation :' DASHI/Interop/FactorisationSpineCrossDomainAdapterExact.agda
grep -q '^record CandidateFamilyExecutionSpine' DASHI/Core/CandidateFamilyExecutionExact.agda
grep -q '^record RequirementConflictBatchSpine' DASHI/Core/RequirementConflictBatchExecutionExact.agda
grep -q '^data CandidateRelation' DASHI/Core/RequirementConflictBatchExecutionExact.agda
grep -q '^admittedBatchProjectsToCandidateFamilyExecution :' DASHI/Core/RequirementConflictBatchExecutionExact.agda
grep -q '^fromRSAReducerRelation :' DASHI/ComputerScience/RSA260RequirementConflictBatchSpineExact.agda
grep -q '^syntheticBatchExecution :' DASHI/ComputerScience/RSA260RequirementConflictBatchSpineExact.agda
grep -q '^flyCandidateFamilyExecutionSpine :' DASHI/ComputerScience/FlyCandidateFamilyExecutionAdapterExact.agda
grep -q '^admitFlyFamilyComposition :' DASHI/ComputerScience/FlyCandidateFamilyExecutionAdapterExact.agda

grep -q '^exactReducedDecisionSelectsSameIntervention :' DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda
grep -q '^approximateReducedDecisionSelectsSameIntervention :' DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda
grep -q '^data DerivedDecisionAdequacy' DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda
grep -q '^record FirstOrderAdequacyInterface' DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda
grep -q 'firstOrderPolicyTokenMayExistWithoutRichAdequacyProofIsFalse' DASHI/Core/ConsumerDecisionAdequacyFromReductionExact.agda

grep -q '^exactROMActBranch :' DASHI/Core/ConsumerAdequacyJointPolicyBidiCompilerExact.agda
grep -q '^approximateROMActBranch :' DASHI/Core/ConsumerAdequacyJointPolicyBidiCompilerExact.agda
grep -q '^counterexampleOpensFidelityBranch :' DASHI/Core/ConsumerAdequacyJointPolicyBidiCompilerExact.agda
grep -q 'missingCertificateAloneOpensFidelityBranchIsFalse' DASHI/Core/ConsumerAdequacyJointPolicyBidiCompilerExact.agda

grep -q '^jCoarseFineReopening :' DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda
grep -q '^jFineSensitiveConsumerRefutesJCoarseOnly :' DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda
grep -q '^jCoarseExactReductionRetainingJFine :' DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda
grep -q 'jFineIsMerelyAnotherNameForMaximumComputeFidelityIsFalse' DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda

grep -q '^module DASHI.CoarseFineFabricEverything where' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.CoarseFineFabricCalculusExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.FactorisationSpineCrosswalkExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Interop.FactorisationSpineCrossDomainAdapterExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.ExperimentalCoordinateProjectionBridgeExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.CandidateFamilyExecutionExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.RequirementConflictBatchExecutionExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Core.CoarseDynamicsTraceCongruenceExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Interop.LocalGlobalBundleGluingExact' DASHI/CoarseFineFabricEverything.agda
grep -q 'DASHI.Interop.ProofArchaeologyCoarseFineAdapterExact' DASHI/CoarseFineFabricEverything.agda

grep -q '^data SequentialConsumerPlan' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^OutcomePossible :' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^oneShotConsumerClosingPlan :' DASHI/Core/SequentialConsumerExperimentPlannerExact.agda
grep -q '^data SequentialActionabilityPlan' DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
grep -q '^robustActionSurvivesMeasuredRefinement :' DASHI/Core/SequentialRobustActionabilityPlannerExact.agda
grep -q '^data SequentialRelationalPlan' DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
grep -q 'everyHypothesisMustPredictOneDeterministicOutcomeIsFalse' DASHI/Core/SequentialRelationalExperimentPlannerExact.agda
grep -q '^data JointSequentialPolicy' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q '^data EvidenceCapableKind' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q '^bundleAsEvidenceMove :' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q '^record FidelityUnlocksDecision' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q 'fidelityMoveAloneRefinesEmpiricalHypothesisFibreIsFalse' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q 'fidelityCanRemoveModelAdequacyObstructionIsTrue' DASHI/Core/JointSequentialInformationFidelityPolicyExact.agda
grep -q '^reductionEscalationAsFidelityMove :' DASHI/Core/ConsumerReductionJointPolicyBridgeExact.agda
grep -q '^jointPolicy :' DASHI/Core/JointSequentialInformationFidelityFixtureExact.agda
grep -q '^fidelityUnlocksActionB :' DASHI/Core/JointSequentialInformationFidelityFixtureExact.agda
grep -q 'measurementOutcomeCanDetermineWhetherEscalationIsNeededIsTrue' DASHI/Core/JointSequentialInformationFidelityFixtureExact.agda
grep -q '^record SequentialPhysicalExperimentProgramme' DASHI/Physics/Foundations/GRQFTSequentialExperimentPlannerExact.agda
grep -q '^record LESSequentialConsumerExperiment' DASHI/Environment/LESSequentialExperimentPlannerExact.agda
grep -q '^record LESSequentialActionabilityExperiment' DASHI/Environment/LESSequentialExperimentPlannerExact.agda
grep -q '^record LESJointMeasurementFidelityCampaign' DASHI/Environment/LESJointSequentialMeasurementFidelityPolicyExact.agda
grep -q '^record LESFidelityUnlocksControl' DASHI/Environment/LESJointSequentialMeasurementFidelityPolicyExact.agda
grep -q '^bucketToRichardsFidelityMove :' DASHI/Environment/LESJointSequentialMeasurementFidelityPolicyExact.agda
grep -q '^record LESDecisionAdequacyBridge' DASHI/Environment/LESProofDerivedDecisionAdequacyExact.agda
grep -q '^lesExactROMActBranch :' DASHI/Environment/LESProofDerivedDecisionAdequacyExact.agda
grep -q '^lesApproximateROMActBranch :' DASHI/Environment/LESProofDerivedDecisionAdequacyExact.agda
grep -q 'policyDecisionAdequacyMayBeFreeOfROMOrMarginProofIsFalse' DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda
grep -q 'fineStateMeansOnlyMoreExpensiveModelIsFalse' DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda
grep -q 'relativeFineInformationEqualsModelFidelityIsFalse' DASHI/Environment/LESAdaptiveConsumerLoopCrossPollinationExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Core/SequentialExperimentPlanningValidation.agda
scripts/run_agda29_parallel_check.sh DASHI/CoarseFineFabricEverything.agda
