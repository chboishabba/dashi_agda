#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallBidiExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallValidationExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGAuthorityClosureExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGModelProvenanceBidiExact.agda
  DASHI/Physics/ExoticGravity/SuperconductingChargeMassCurrentBidiExact.agda
  DASHI/Physics/ExoticGravity/SuperconductingGravityExperimentalConstraintRegistryExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryStressEnergyScopeBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryStressEnergyCompilationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryGRComparatorCompilationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryGRComparatorStateBridgeExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryBackgroundClosureExact.agda
  DASHI/Physics/ExoticGravity/AntigravityLaboratoryOrdinaryModelClosureWeldExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
  DASHI/Physics/ExoticGravity/LiTorr1991CombinedFieldSourceEntitlementExact.agda
  DASHI/Physics/ExoticGravity/LiTorr1992CoupledPotentialSourceEntitlementExact.agda
  DASHI/Culture/AmyEskridgeHAL5AntigravitySourceEntitlementExact.agda
  DASHI/Culture/AmyEskridgeHAL5PrimaryLiteratureSnowballExact.agda
  DASHI/Culture/AmyEskridgeHistoricalMechanismBidiSourceWeldExact.agda
  DASHI/Culture/AmyEskridgeMechanismAssociationProvenanceExact.agda
  DASHI/Culture/AmyEskridgeForensicAcquisitionPriorityExact.agda
  DASHI/Culture/AmyEskridgeEvidenceEverything.agda
)
for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

grep -q 'massCurrentReceiptAutomaticallyConstructsFullStressEnergy' DASHI/Physics/ExoticGravity/SuperconductingChargeMassCurrentBidiExact.agda
grep -q 'massCurrentAloneConstructsStressEnergy' DASHI/Physics/ExoticGravity/AntigravityLaboratoryStressEnergyCompilationExact.agda
grep -q 'evaluationRequestEqualsCompletedPrediction' DASHI/Physics/ExoticGravity/AntigravityLaboratoryGRComparatorCompilationExact.agda
grep -q 'requestStageMatchesExistingPlan' DASHI/Physics/ExoticGravity/AntigravityLaboratoryGRComparatorStateBridgeExact.agda
grep -q 'typedPredictionPaysBackgroundClosure' DASHI/Physics/ExoticGravity/AntigravityLaboratoryGRComparatorStateBridgeExact.agda
grep -q 'closedComparatorStateIsClosed' DASHI/Physics/ExoticGravity/AntigravityLaboratoryBackgroundClosureExact.agda
grep -q 'closedComparatorAutomaticallyProvesMaterialEffectiveNegativeG' DASHI/Physics/ExoticGravity/AntigravityLaboratoryBackgroundClosureExact.agda
grep -q 'typedComparatorClosureAloneCreatesOptimizedBundle' DASHI/Physics/ExoticGravity/AntigravityLaboratoryOrdinaryModelClosureWeldExact.agda
grep -q 'fullOrdinaryClosureStillLeavesConstitutiveRatio' DASHI/Physics/ExoticGravity/AntigravityLaboratoryOrdinaryModelClosureWeldExact.agda
grep -q 'etaCStringAlonePaysConstitutiveRatio' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact.agda
grep -q 'typedRatioAloneMayCompileExistingNegativeGWeld' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact.agda
grep -q 'canonicalScalingReplicationIdentityStillRequired' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGConstitutiveRatioMeasurementExact.agda
grep -q 'sameReplicationCarrier' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
grep -q 'sameScalingSweepCarrier' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
grep -q 'compileConstitutiveNegativeGReceipt' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
grep -q 'identityWeldMayCompileExistingNegativeGWeld' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
grep -q 'closedScalingStateAutomaticallyProvesNegativeEffectiveG' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScalingReplicationIdentityWeldExact.agda
grep -q 'currentScientificWallStartsAtMassCurrent' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallBidiExact.agda
grep -q 'currentScientificWallProducerIsEmpiricalEvidence' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallBidiExact.agda
grep -q 'closedWallHasNoFurtherAcquisition' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'closedWallProducerIsNoSearch' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'authorityClosurePaysSourceCurrent' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGAuthorityClosureExact.agda

# Amy memorial source-attribution / snowball boundaries.
grep -q 'hostAuthenticatedDeckEqualsIndependentPhysicsValidation' DASHI/Culture/AmyEskridgeHAL5AntigravitySourceEntitlementExact.agda
grep -q 'reportedPrimaryAnomalyEqualsEstablishedPhysicalEffect' DASHI/Culture/AmyEskridgeHAL5PrimaryLiteratureSnowballExact.agda
grep -q 'abstractClaimCreatesObservationReceipt' DASHI/Culture/AmyEskridgeHistoricalMechanismBidiSourceWeldExact.agda
grep -q 'amyDiscussionEqualsAmyEndorsement' DASHI/Culture/AmyEskridgeMechanismAssociationProvenanceExact.agda
grep -q 'outOfOrderForensicAcquisitionMayBeRetained' DASHI/Culture/AmyEskridgeForensicAcquisitionPriorityExact.agda
grep -q 'podkletnovNieminen1992ReportedSignal' DASHI/Physics/ExoticGravity/SuperconductingGravityExperimentalConstraintRegistryExact.agda
grep -q 'reportedSignalEqualsEstablishedEffect' DASHI/Physics/ExoticGravity/SuperconductingGravityExperimentalConstraintRegistryExact.agda

chmod +x scripts/agda29_without_k_wrapper.sh scripts/run_agda29_parallel_check.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda \
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallValidationExact.agda \
  DASHI/Culture/AmyEskridgeEvidenceEverything.agda

echo "Material-effective negative-G + Amy memorial source/provenance/snowball validation checks passed"
