#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/BrainCognitionObservationSpineExact.agda"

[[ -f "$owner" ]]

grep -q 'DASHI.Cognition.PNF.MemoryFibre' "$owner"
grep -q 'DASHI.Cognition.PNF.LearningAlgebra' "$owner"
grep -q 'DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact' "$owner"
grep -q 'DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient' "$owner"
grep -q 'DASHI.Reasoning.AuthorityBooleanPolarityRepairExact' "$owner"
grep -q 'DASHI.Reasoning.MaleCNSTypedHyperfabricChartProjectionExact' "$owner"
grep -q 'memoryContentMayPersistWhileInfluenceChanges' "$owner"
grep -q 'observedActionDoesNotRecoverFineDecisionState' "$owner"
grep -q 'observationEqualityDoesNotAuthorizeLatentIdentity' "$owner"
grep -q 'connectomeDoesNotDecodeMemoryContent' "$owner"
grep -q 'connectomeDoesNotDecodeMotorPlan' "$owner"
grep -q 'observationDoesNotAuthorizeTraumaInference' "$owner"
grep -q 'ninetyPercentUnusedBrainClaimPaid' "$owner"
grep -q 'minimalLearnedLatentExtractionPaid' "$owner"
grep -q 'candidateLatentConsumerQuestion' "$owner"
