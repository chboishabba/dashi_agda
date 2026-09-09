#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallBidiExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallPaymentReceiptExact.agda
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallValidationExact.agda
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

grep -q 'outOfOrderRetainedAcquisition' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'outOfOrderAcquisitionDoesNotSkipMassCurrentPayment' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'physicalAcquisitionMustFollowPromotionOrder' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'closedWallHasNoFurtherAcquisition' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallProgressionExact.agda
grep -q 'terminalPaymentRequiresActualReceipts' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallPaymentReceiptExact.agda
grep -q 'stressEnergyUsesSameMassCurrent' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallPaymentReceiptExact.agda
grep -q 'sameNegativeGInterpretation' DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallPaymentReceiptExact.agda

chmod +x scripts/agda29_without_k_wrapper.sh scripts/run_agda29_parallel_check.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGSourceValidationExact.agda \
  DASHI/Physics/ExoticGravity/MaterialEffectiveNegativeGScientificWallValidationExact.agda

echo "Material-effective negative-G scientific-wall BIDI validation checks passed"
