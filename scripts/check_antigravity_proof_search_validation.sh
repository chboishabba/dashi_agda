#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
  DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
  DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGBidiValidationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityConstraintPruningVsBundlePaymentExact.agda
  DASHI/Physics/ExoticGravity/ConstraintPruningIdentityWeldExact.agda
  DASHI/Physics/ExoticGravity/AntigravityConstraintInformedBundleDesignExact.agda
  DASHI/Physics/ExoticGravity/AntigravityJointProofSearchFrontierExact.agda
  DASHI/Physics/ExoticGravity/AntigravityMicroscopicBulkProofSearchBridgeExact.agda
  DASHI/Physics/ExoticGravity/AntigravityFirstIrreducibleSourceResidualExact.agda
  DASHI/Physics/ExoticGravity/LiTorrTheorySourceDiligenceProofSearchExact.agda
  DASHI/Physics/ExoticGravity/AntigravityEmpiricalTheoryDiligenceBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityProofSearchLeastPrivilegeAdmissionExact.agda
  DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
  DASHI/Physics/ExoticGravity/AntigravitySourceBundleDerivationLineageExact.agda
  DASHI/Physics/ExoticGravity/AntigravityExperimentalCutProvenanceExact.agda
  DASHI/Physics/ExoticGravity/AntigravityBundleExecutionDerivationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityFullyDerivedExperimentalCutExact.agda
  DASHI/Physics/ExoticGravity/AntigravityExecutionCalibrationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityCalibratedExecutionBridgeExact.agda
  DASHI/Physics/ExoticGravity/AntigravityCalibratedFullyDerivedExperimentalCutExact.agda
  DASHI/Physics/ExoticGravity/AntigravityConsumerScopedCalibrationExact.agda
  DASHI/Physics/ExoticGravity/AntigravityClaimScopedExperimentalCutExact.agda
  DASHI/Physics/ExoticGravity/AntigravityClaimScopedComparativeAnomalyExact.agda
  DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
  DASHI/Physics/ExoticGravity/AntigravityProofSearchValidationExact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
  if grep -En '(^|[[:space:]])(postulate|primitive)[[:space:]]|\{!!\}|trustMe|unsafe|TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|funext|Properties\.WithK|unique⇒irrelevant|--with-K' "$file"; then
    echo "forbidden proof escape in $file" >&2
    exit 1
  fi
done

# Signed-G / negative-G BIDI invariants.
grep -q 'flipCouplingSignInvolutive' \
  DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'negativeGReversesEveryDisplayedLeadingCorrection' \
  DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'frozenSignProbeEqualsSelfConsistentNegativeGTheory' \
  DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'sourceSideSignCollision' \
  DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
grep -q 'negativeGAutomaticallyFlipsCosmologicalConstant' \
  DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
grep -q 'constantSlotNameDeterminesCouplingSign' \
  DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda
grep -q 'negativeGCounterfactualOverwritesMeasuredRegistryValue' \
  DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda
grep -q 'negativeGAloneImpliesAlteredInertialMass' \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
grep -q 'negativeGAloneImpliesReactionlessPropulsion' \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
grep -q 'sameInputPairIsolatesCouplingSignBetterThanUnpairedComparison' \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
grep -q 'betterNegativeGFitAutomaticallyEstablishesNegativeGPhysics' \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda

# Introspective frontier / no-stitch invariants.
grep -q 'currentRecommendedBundle = sourceGeometryBundle' \
  DASHI/Physics/ExoticGravity/AntigravityJointProofSearchFrontierExact.agda
grep -q 'currentMicroscopicFirstOpenIsSourceDistribution' \
  DASHI/Physics/ExoticGravity/AntigravityMicroscopicBulkProofSearchBridgeExact.agda
grep -q 'sourceShapeEqualsSourceDistribution' \
  DASHI/Physics/ExoticGravity/AntigravityFirstIrreducibleSourceResidualExact.agda
grep -q 'heterogeneousExperimentsMayBeStitchedIntoOneApparatusReceipt' \
  DASHI/Physics/ExoticGravity/AntigravityConstraintPruningVsBundlePaymentExact.agda
grep -q 'ConstraintPruningIdentityWeld' \
  DASHI/Physics/ExoticGravity/ConstraintPruningIdentityWeldExact.agda

# Attribution / lane-separation invariants.
grep -q '10.1103/PhysRevD.43.457' \
  DASHI/Physics/ExoticGravity/LiTorrTheorySourceDiligenceProofSearchExact.agda
grep -q '10.1103/PhysRevB.46.5489' \
  DASHI/Physics/ExoticGravity/LiTorrTheorySourceDiligenceProofSearchExact.agda
grep -q 'physicalSourceAndTheorySourceAreSameCoordinate' \
  DASHI/Physics/ExoticGravity/AntigravityEmpiricalTheoryDiligenceBidiExact.agda

# Execution/provenance/derivation invariants.
grep -q 'apparatusIdentityEqualsRunIdentifier' \
  DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'calibrationCarrierEqualsCalibrationRevision' \
  DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'rawDataHash' \
  DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'outputBundleMatches' \
  DASHI/Physics/ExoticGravity/AntigravitySourceBundleDerivationLineageExact.agda
grep -q 'eachBundleNeedsRunDataHashRevision' \
  DASHI/Physics/ExoticGravity/AntigravityExperimentalCutProvenanceExact.agda
grep -q 'exactOutputBundleIdentityRequired' \
  DASHI/Physics/ExoticGravity/AntigravityBundleExecutionDerivationExact.agda
grep -q 'fullyDerivedCutAutomaticallyProvesAntigravity' \
  DASHI/Physics/ExoticGravity/AntigravityFullyDerivedExperimentalCutExact.agda

# Typed calibration / same-object execution invariants.
grep -q 'ExecutionCalibrationReceipt' \
  DASHI/Physics/ExoticGravity/AntigravityExecutionCalibrationExact.agda
grep -q 'SourceExecutionIdentityWeld' \
  DASHI/Physics/ExoticGravity/AntigravityCalibratedExecutionBridgeExact.agda
grep -q 'sourceExecutionApparatusMatches' \
  DASHI/Physics/ExoticGravity/AntigravityCalibratedExecutionBridgeExact.agda
grep -q 'allFourStagesNeedTypedCalibration' \
  DASHI/Physics/ExoticGravity/AntigravityCalibratedFullyDerivedExperimentalCutExact.agda

# Consumer-scoped calibration / final comparison identity.
grep -q 'ConsumerScopedCalibration' \
  DASHI/Physics/ExoticGravity/AntigravityConsumerScopedCalibrationExact.agda
grep -q 'coarseCalibrationDoesNotDetermineDiscriminator' \
  DASHI/Physics/ExoticGravity/AntigravityConsumerScopedCalibrationExact.agda
grep -q 'allFourStagesMustMatchSameClaimConsumer' \
  DASHI/Physics/ExoticGravity/AntigravityClaimScopedExperimentalCutExact.agda
grep -q 'sameCalibratedCut' \
  DASHI/Physics/ExoticGravity/AntigravityClaimScopedComparativeAnomalyExact.agda
grep -q 'newConsumersRequireConsumerScopedCalibration' \
  DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'exactClaimScopedCutIdentityRequired' \
  DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'calibrationStringAloneSufficient' \
  DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'legacyComparativeReceiptAutomaticallyUpgrades' \
  DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda

# Least privilege must remain upstream of execution/success.
grep -q 'admittedMoveEqualsExecutedExperiment' \
  DASHI/Physics/ExoticGravity/AntigravityProofSearchLeastPrivilegeAdmissionExact.agda
grep -q 'admittedMoveEqualsSuccessfulReceipt' \
  DASHI/Physics/ExoticGravity/AntigravityProofSearchLeastPrivilegeAdmissionExact.agda

chmod +x scripts/agda29_without_k_wrapper.sh scripts/run_agda29_parallel_check.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/ExoticGravity/AntigravityProofSearchValidationExact.agda \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGBidiValidationExact.agda

echo "Antigravity proof-search and negative-G BIDI validation checks passed"
