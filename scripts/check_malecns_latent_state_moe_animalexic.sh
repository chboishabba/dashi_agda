#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSLatentStateMoEGrokkingAnimalexicCrossPollinationExact.agda"

[[ -f "$owner" ]]

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
grep -q 'empiricalAffectLabelPaid = false' "$owner"
