#!/usr/bin/env bash
set -euo pipefail

repair="DASHI/Reasoning/AuthorityBooleanPolarityRepairExact.agda"
spine="DASHI/Reasoning/BrainCognitionObservationSpineExact.agda"

[[ -f "$repair" ]]
[[ -f "$spine" ]]

grep -q 'legacyBlockedBooleanPolarityInverted' "$repair"
grep -q 'blockedMeansAuthorityUnavailable' "$repair"
grep -q 'functionalConnectomeMindReadingBlocked' "$repair"
grep -q 'fmriProxyHiddenChartRecoveryBlocked' "$repair"

grep -q 'DASHI.Core.ConsumerFamilyRefinementKernelExact' "$spine"
grep -q 'DASHI.Reasoning.MaleCNSConsumerRelativeLatentParetoExact' "$spine"
grep -q 'rememberedEventConsumer' "$spine"
grep -q 'memoryInfluenceConsumer' "$spine"
grep -q 'motorPolicyConsumer' "$spine"
grep -q 'fineDecisionStateConsumer' "$spine"
grep -q 'currentStructuralLatentFactorsWholeCognitionFamily' "$spine"
grep -q 'observedActionDoesNotFactorFineDecisionState' "$spine"
grep -q 'minimalLearnedLatentExtractionPaid' "$spine"
grep -q 'ninetyPercentUnusedBrainClaimPaid' "$spine"
grep -q 'structuralLatentDimensionEqualsPhysicalBrainDimension' "$spine"
grep -q 'gautheyBehaviorRecordedAndSynchronized' "$spine"
grep -q 'exactBehaviorDepositMemberResolved' "$spine"
