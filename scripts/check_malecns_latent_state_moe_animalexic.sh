#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact.agda"
bidi="DASHI/Reasoning/MaleCNSJointConsumerBidiRefinementExact.agda"
validation="DASHI/Reasoning/MaleCNSLatentStateMoEGrokkingAnimalexicValidation.agda"

[[ -f "$owner" ]]
[[ -f "$bidi" ]]
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

grep -q 'MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact' "$validation"
grep -q 'MaleCNSJointConsumerBidiRefinementExact' "$validation"
grep -q 'FunctionalConnectomeBodyMemoryBridge' "$validation"
grep -q 'IntersectionalLongitudinalProxyTransitionBridge' "$validation"
grep -q 'AnimalexicDrosophilaEmbodiedBridge' "$validation"
grep -q 'ConsciousAccessCoalition' "$validation"
