#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
  DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
  DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda
  DASHI/Physics/GR/SignedNewtonianLimitBidiExact.agda
  DASHI/Physics/GR/SignedGravitationalWaveCouplingBidiExact.agda
  DASHI/Physics/GR/SignedGravitationalWaveDetectorResponseBidiExact.agda
  DASHI/Physics/GR/GravitationalWavePolarizationSourceAttributionExact.agda
  DASHI/Physics/GR/GravitationalWavePolarizationSignBidiExact.agda
  DASHI/Physics/GR/NegativeGGravitationalWaveTestRoutingExact.agda
  DASHI/Physics/GR/SignedCosmologicalMatterCouplingBidiExact.agda
  DASHI/Physics/GR/UniversalSignedGCrossScaleFingerprintBidiExact.agda
  DASHI/Physics/GR/NegativeGPredictionAuthorityExact.agda
  DASHI/Physics/GR/SignedGSourceDynamicsBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingScopeBidiExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGClaimComparisonWeldExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGCrossScaleProofSearchExact.agda
  DASHI/Physics/ExoticGravity/AntigravityNegativeGBidiValidationExact.agda
  DASHI/Physics/ExoticGravity/GravitationalWavePolarizationAndScopeValidationExact.agda
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
grep -q 'flipCouplingSignInvolutive' DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'negativeGReversesEveryDisplayedLeadingCorrection' DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'frozenSignProbeEqualsSelfConsistentNegativeGTheory' DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'selfConsistentNegativeGRequiresStabilityAnalysis' DASHI/Physics/GR/SignedEinsteinCouplingBidiExact.agda
grep -q 'sourceSideSignCollision' DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
grep -q 'negativeGAutomaticallyFlipsCosmologicalConstant' DASHI/Physics/GR/SignedEinsteinCouplingSourceDegeneracyBidiExact.agda
grep -q 'constantSlotNameDeterminesCouplingSign' DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda
grep -q 'negativeGCounterfactualOverwritesMeasuredRegistryValue' DASHI/Physics/GR/SignedGRNormalizationBidiExact.agda

# Newtonian / GW / cosmology cross-scale sign fibres.
grep -q 'exactExistingPoissonReceiptRequired' DASHI/Physics/GR/SignedNewtonianLimitBidiExact.agda
grep -q 'poissonSignCollision' DASHI/Physics/GR/SignedNewtonianLimitBidiExact.agda
grep -q 'vacuumPropagationCollision' DASHI/Physics/GR/SignedGravitationalWaveCouplingBidiExact.agda
grep -q 'exactExistingWaveEquationAndStrainReceiptsRequired' DASHI/Physics/GR/SignedGravitationalWaveCouplingBidiExact.agda
grep -q 'readoutSignCollision' DASHI/Physics/GR/SignedGravitationalWaveDetectorResponseBidiExact.agda
grep -q 'rawReadoutSignAloneDeterminesSourceStrainSign' DASHI/Physics/GR/SignedGravitationalWaveDetectorResponseBidiExact.agda
grep -q 'currentGWAgreementAutomaticallyRulesOutEveryNegativeGConstruction' DASHI/Physics/GR/NegativeGGravitationalWaveTestRoutingExact.agda
grep -q 'cosmologicalMatterTermCollision' DASHI/Physics/GR/SignedCosmologicalMatterCouplingBidiExact.agda
grep -q 'exactExistingCosmologicalDynamicsObjectsRequired' DASHI/Physics/GR/SignedCosmologicalMatterCouplingBidiExact.agda
grep -q 'universalNegativeGRequiresSameSignAcrossScales' DASHI/Physics/GR/UniversalSignedGCrossScaleFingerprintBidiExact.agda

# GW polarization attribution / polarity non-collapse.
grep -q '10.1103/PhysRevLett.119.141101' DASHI/Physics/GR/GravitationalWavePolarizationSourceAttributionExact.agda
grep -q 'citationImportsDASHIBidiProof' DASHI/Physics/GR/GravitationalWavePolarizationSourceAttributionExact.agda
grep -q 'plusBasisDoesNotDetermineWaveformSign' DASHI/Physics/GR/GravitationalWavePolarizationSignBidiExact.agda
grep -q 'waveformSignDoesNotDeterminePolarizationBasis' DASHI/Physics/GR/GravitationalWavePolarizationSignBidiExact.agda
grep -q 'readoutSignCollision' DASHI/Physics/GR/GravitationalWavePolarizationSignBidiExact.agda
grep -q 'polarizationBasisCannotRecoverGSign' DASHI/Physics/GR/GravitationalWavePolarizationSignBidiExact.agda

# Internal counterfactual attribution and sign-conditioned source dynamics.
grep -q 'anyInternalTheoremMayAuthorizeNegativeGPrediction' DASHI/Physics/GR/NegativeGPredictionAuthorityExact.agda
grep -q 'exactSignedGOwnerRequired' DASHI/Physics/GR/NegativeGPredictionAuthorityExact.agda
grep -q 'sameSourceModelMeansSameSolvedSourceState' DASHI/Physics/GR/SignedGSourceDynamicsBidiExact.agda
grep -q 'sourceSolutionDerivationRequiredPerSign' DASHI/Physics/GR/SignedGSourceDynamicsBidiExact.agda

# Universal versus material/source-scoped coupling.
grep -q 'localScopeCollision' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingScopeBidiExact.agda
grep -q 'localNegativeEffectiveCouplingEqualsUniversalNegativeG' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingScopeBidiExact.agda
grep -q 'materialEffectiveNegativeGRequiresRegimeSpecificReplication' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingScopeBidiExact.agda
grep -q 'rejectionOfUniversalNegativeGRejectsMaterialEffectiveNegativeG' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingScopeBidiExact.agda

# Antigravity claim / comparison / cross-scale proof-search invariants.
grep -q 'negativeGAloneImpliesAlteredInertialMass' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
grep -q 'negativeGAloneImpliesReactionlessPropulsion' DASHI/Physics/ExoticGravity/AntigravityNegativeGCouplingBidiExact.agda
grep -q 'sameLawReSolvedSourcePairIsolatesCouplingSignBetterThanUnpairedComparison' DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
grep -q 'exactSignedGOwnerAuthorityRequired' DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
grep -q 'betterNegativeGFitAutomaticallyEstablishesNegativeGPhysics' DASHI/Physics/ExoticGravity/AntigravityNegativeGPairedComparatorExact.agda
grep -q 'positiveGIsOrdinaryComparisonPrediction' DASHI/Physics/ExoticGravity/AntigravityNegativeGClaimComparisonWeldExact.agda
grep -q 'negativeGIsAlternativeComparisonPrediction' DASHI/Physics/ExoticGravity/AntigravityNegativeGClaimComparisonWeldExact.agda
grep -q 'firstUniversalNegativeGStage' DASHI/Physics/ExoticGravity/AntigravityNegativeGCrossScaleProofSearchExact.agda
grep -q 'positiveDensityAttractionCanDiscriminateFrozenNegativeGSign' DASHI/Physics/ExoticGravity/AntigravityNegativeGCrossScaleProofSearchExact.agda

# Introspective frontier / no-stitch invariants.
grep -q 'currentRecommendedBundle = sourceGeometryBundle' DASHI/Physics/ExoticGravity/AntigravityJointProofSearchFrontierExact.agda
grep -q 'currentMicroscopicFirstOpenIsSourceDistribution' DASHI/Physics/ExoticGravity/AntigravityMicroscopicBulkProofSearchBridgeExact.agda
grep -q 'sourceShapeEqualsSourceDistribution' DASHI/Physics/ExoticGravity/AntigravityFirstIrreducibleSourceResidualExact.agda
grep -q 'heterogeneousExperimentsMayBeStitchedIntoOneApparatusReceipt' DASHI/Physics/ExoticGravity/AntigravityConstraintPruningVsBundlePaymentExact.agda
grep -q 'ConstraintPruningIdentityWeld' DASHI/Physics/ExoticGravity/ConstraintPruningIdentityWeldExact.agda

# Attribution / lane-separation invariants.
grep -q '10.1103/PhysRevD.43.457' DASHI/Physics/ExoticGravity/LiTorrTheorySourceDiligenceProofSearchExact.agda
grep -q '10.1103/PhysRevB.46.5489' DASHI/Physics/ExoticGravity/LiTorrTheorySourceDiligenceProofSearchExact.agda
grep -q 'physicalSourceAndTheorySourceAreSameCoordinate' DASHI/Physics/ExoticGravity/AntigravityEmpiricalTheoryDiligenceBidiExact.agda

# Execution/provenance/derivation invariants.
grep -q 'apparatusIdentityEqualsRunIdentifier' DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'calibrationCarrierEqualsCalibrationRevision' DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'rawDataHash' DASHI/Physics/ExoticGravity/AntigravitySourceAcquisitionCompilationExact.agda
grep -q 'outputBundleMatches' DASHI/Physics/ExoticGravity/AntigravitySourceBundleDerivationLineageExact.agda
grep -q 'eachBundleNeedsRunDataHashRevision' DASHI/Physics/ExoticGravity/AntigravityExperimentalCutProvenanceExact.agda
grep -q 'exactOutputBundleIdentityRequired' DASHI/Physics/ExoticGravity/AntigravityBundleExecutionDerivationExact.agda
grep -q 'fullyDerivedCutAutomaticallyProvesAntigravity' DASHI/Physics/ExoticGravity/AntigravityFullyDerivedExperimentalCutExact.agda

# Typed calibration / same-object execution invariants.
grep -q 'ExecutionCalibrationReceipt' DASHI/Physics/ExoticGravity/AntigravityExecutionCalibrationExact.agda
grep -q 'SourceExecutionIdentityWeld' DASHI/Physics/ExoticGravity/AntigravityCalibratedExecutionBridgeExact.agda
grep -q 'sourceExecutionApparatusMatches' DASHI/Physics/ExoticGravity/AntigravityCalibratedExecutionBridgeExact.agda
grep -q 'allFourStagesNeedTypedCalibration' DASHI/Physics/ExoticGravity/AntigravityCalibratedFullyDerivedExperimentalCutExact.agda

# Consumer-scoped calibration / final comparison identity.
grep -q 'ConsumerScopedCalibration' DASHI/Physics/ExoticGravity/AntigravityConsumerScopedCalibrationExact.agda
grep -q 'coarseCalibrationDoesNotDetermineDiscriminator' DASHI/Physics/ExoticGravity/AntigravityConsumerScopedCalibrationExact.agda
grep -q 'allFourStagesMustMatchSameClaimConsumer' DASHI/Physics/ExoticGravity/AntigravityClaimScopedExperimentalCutExact.agda
grep -q 'sameCalibratedCut' DASHI/Physics/ExoticGravity/AntigravityClaimScopedComparativeAnomalyExact.agda
grep -q 'newConsumersRequireConsumerScopedCalibration' DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'exactClaimScopedCutIdentityRequired' DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'calibrationStringAloneSufficient' DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda
grep -q 'legacyComparativeReceiptAutomaticallyUpgrades' DASHI/Physics/ExoticGravity/AntigravityStrongPromotionFacadeExact.agda

# Least privilege must remain upstream of execution/success.
grep -q 'admittedMoveEqualsExecutedExperiment' DASHI/Physics/ExoticGravity/AntigravityProofSearchLeastPrivilegeAdmissionExact.agda
grep -q 'admittedMoveEqualsSuccessfulReceipt' DASHI/Physics/ExoticGravity/AntigravityProofSearchLeastPrivilegeAdmissionExact.agda

chmod +x scripts/agda29_without_k_wrapper.sh scripts/run_agda29_parallel_check.sh
AGDA_BIN="$root/scripts/agda29_without_k_wrapper.sh" \
  scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/ExoticGravity/AntigravityProofSearchValidationExact.agda \
  DASHI/Physics/ExoticGravity/AntigravityNegativeGBidiValidationExact.agda \
  DASHI/Physics/ExoticGravity/GravitationalWavePolarizationAndScopeValidationExact.agda

echo "Antigravity proof-search, negative-G, GW-polarization, and coupling-scope validation checks passed"
