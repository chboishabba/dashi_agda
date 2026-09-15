#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact.agda"
bidi="DASHI/Reasoning/MaleCNSJointConsumerBidiRefinementExact.agda"
kernel="DASHI/Core/ConsumerFamilyRefinementKernelExact.agda"
trial_context="DASHI/Reasoning/MaleCNSStructureFunctionTrialContextRefinementExact.agda"
validation="DASHI/Reasoning/MaleCNSLatentStateMoEGrokkingAnimalexicValidation.agda"

[[ -f "$owner" ]]
[[ -f "$bidi" ]]
[[ -f "$kernel" ]]
[[ -f "$trial_context" ]]
[[ -f "$validation" ]]

grep -q 'record LatentStateProgrammeBoundary' "$owner"
grep -q 'RoutingState' "$owner"
grep -q 'LatentState' "$owner"
grep -q 'SemanticHypothesis' "$owner"
grep -q 'routingAdequacyDoesNotPromoteMechanism' "$owner"
grep -q 'e8GeometryDoesNotPromoteBiologicalOntology' "$owner"
grep -q 'behaviouralMotifDoesNotPromoteSemanticMeaning' "$owner"
grep -q 'phenomenalIdentityRemainsUnpaid' "$owner"
grep -q 'consumerFamilyAdequacyIsJoint' "$owner"
grep -q 'compressionKindsRemainDistinct' "$owner"
grep -q 'interactiveSemanticRefinement' "$owner"
grep -q 'empiricalAffectLabelPaidIsFalse' "$owner"

grep -q 'choiceOnlyJointConsumerCollision' "$bidi"
grep -q 'choiceOnlyCannotFactorJointOutcome' "$bidi"
grep -q 'choiceRechartCannotRecoverMemory' "$bidi"
grep -q 'repairedLatentFactorsJointOutcome' "$bidi"
grep -q 'record ConnectomeLatentBidiBoundary' "$bidi"
grep -q 'connectomeConstraintIsNotLatentInversion' "$bidi"
grep -q 'interventionFailureCreatesRefinementObligation' "$bidi"
grep -q 'populationTrajectoryDoesNotPromoteMechanism' "$bidi"

grep -q 'record ConsumerFamily' "$kernel"
grep -q 'record FamilyFactorsThrough' "$kernel"
grep -q 'record FamilyCollision' "$kernel"
grep -q 'collisionRulesOutFamilyFactorisation' "$kernel"
grep -q 'familyRechartCannotRecoverCollision' "$kernel"
grep -q 'record ConsumerFamilyRepair' "$kernel"
grep -q 'repairRetainsCoarseObserver' "$kernel"
grep -q 'repairPaysFailedConsumer' "$kernel"

grep -q 'structureOnlyTrialContextCollision' "$trial_context"
grep -q 'structureOnlyCannotPayJointTrialContextConsumer' "$trial_context"
grep -q 'trialContextRechartCannotRecoverFunctionalDifference' "$trial_context"
grep -q 'repairedStructureTrialContextFactorsJointConsumer' "$trial_context"
grep -q 'record MaleCNSStructureFunctionTrialContextBoundary' "$trial_context"
grep -q 'finiteSpecimenIsNotEmpiricalCrossTrialReplication' "$trial_context"

grep -q 'MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact' "$validation"
grep -q 'MaleCNSJointConsumerBidiRefinementExact' "$validation"
grep -q 'ConsumerFamilyRefinementKernelExact' "$validation"
grep -q 'MaleCNSStructureFunctionTrialContextRefinementExact' "$validation"
grep -q 'FunctionalConnectomeBodyMemoryBridge' "$validation"
grep -q 'IntersectionalLongitudinalProxyTransitionBridge' "$validation"
grep -q 'AnimalexicDrosophilaEmbodiedBridge' "$validation"
grep -q 'ConsciousAccessCoalition' "$validation"
