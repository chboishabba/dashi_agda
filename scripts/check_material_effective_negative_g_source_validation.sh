#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGAuthorityClosureExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGModelProvenanceBidiExact.agda
  DASHI/Physics/ExoticGravity/SuperconductingChargeMassCurrentBidiExact.agda
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
grep -q 'authorityClosurePaysSourceCurrent' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGAuthorityClosureExact.agda

chmod +x scripts/agda29_without_k_wrapper.sh scripts/run_agda29_parallel_check.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda

echo "Material-effective negative-G source/provenance/GR/background/constitutive/replication validation checks passed"
