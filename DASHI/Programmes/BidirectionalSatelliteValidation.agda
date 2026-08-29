module DASHI.Programmes.BidirectionalSatelliteValidation where

open import DASHI.Core.Prelude

open import DASHI.Programmes.BidirectionalSatelliteCorrectionExact
open import DASHI.Programmes.BrainKernelSemanticsCorrectionExact
open import DASHI.Programmes.CFDChartCorrectionExact
open import DASHI.Programmes.DashifineBenchmarkCorrectionExact
open import DASHI.Programmes.GrokkingValidationCorrectionExact
open import DASHI.Programmes.CoreReferenceCorrectionExact
open import DASHI.Programmes.FRACDASHCompilerCorrectionExact
open import DASHI.Programmes.TestHarnessEvidenceCorrectionExact
open import DASHI.Programmes.BrainHemibrainExperimentExact
open import DASHI.Programmes.QuantumFalsifiableTargetExact
open import DASHI.Programmes.RTXLightTransportRefinementExact

------------------------------------------------------------------------
-- BIDI programme receipts.  This root intentionally validates both the generic
-- correction compiler and the repo-specific anti-promotion boundaries.
------------------------------------------------------------------------

bidiNeedsReceipts : correctedModelStillNeedsReceipt cfdBIDIAudit ≡ true
bidiNeedsReceipts = correctedModelStillNeedsReceiptIsTrue cfdBIDIAudit

brainKernelNoAutomaticIdempotence :
  BrainKernelCorrectionBoundary.localSignKernelIsAutomaticallyIdempotent
    canonicalBrainKernelCorrectionBoundary ≡ false
brainKernelNoAutomaticIdempotence =
  BrainKernelCorrectionBoundary.localSignKernelIsAutomaticallyIdempotentIsFalse
    canonicalBrainKernelCorrectionBoundary

cfdNoClosureRecoveryOfLostInformation :
  CFDChartCorrectionBoundary.closureModelCanRecoverDiscardedClaimInformation
    canonicalCFDChartCorrectionBoundary ≡ false
cfdNoClosureRecoveryOfLostInformation =
  CFDChartCorrectionBoundary.closureModelCanRecoverDiscardedClaimInformationIsFalse
    canonicalCFDChartCorrectionBoundary

dashifineNoUniversalPromotion :
  DashifineBenchmarkCorrectionBoundary.oneTaskDominanceIsUniversalLearning
    canonicalDashifineBenchmarkCorrectionBoundary ≡ false
dashifineNoUniversalPromotion =
  DashifineBenchmarkCorrectionBoundary.oneTaskDominanceIsUniversalLearningIsFalse
    canonicalDashifineBenchmarkCorrectionBoundary

grokkingNoMSEPromotion :
  GrokkingValidationCorrectionBoundary.lowMSEFitIsExactFamilyIdentity
    canonicalGrokkingValidationCorrectionBoundary ≡ false
grokkingNoMSEPromotion =
  GrokkingValidationCorrectionBoundary.lowMSEFitIsExactFamilyIdentityIsFalse
    canonicalGrokkingValidationCorrectionBoundary

coreFingerprintNotSemanticEquality :
  CoreReferenceCorrectionBoundary.backendFingerprintEqualityIsStateEquality
    canonicalCoreReferenceCorrectionBoundary ≡ false
coreFingerprintNotSemanticEquality =
  CoreReferenceCorrectionBoundary.backendFingerprintEqualityIsStateEqualityIsFalse
    canonicalCoreReferenceCorrectionBoundary

fracdashOneStepLiftsToFiniteTrace :
  FRACDASHCompilerCorrectionBoundary.oneStepCommutationYieldsFiniteTraceCommutation
    canonicalFRACDASHCompilerCorrectionBoundary ≡ true
fracdashOneStepLiftsToFiniteTrace =
  FRACDASHCompilerCorrectionBoundary.oneStepCommutationYieldsFiniteTraceCommutationIsTrue
    canonicalFRACDASHCompilerCorrectionBoundary

testHarnessArtifactNotProof :
  TestHarnessEvidenceCorrectionBoundary.plotOrMetricIsProofByItself
    canonicalTestHarnessEvidenceCorrectionBoundary ≡ false
testHarnessArtifactNotProof =
  TestHarnessEvidenceCorrectionBoundary.plotOrMetricIsProofByItselfIsFalse
    canonicalTestHarnessEvidenceCorrectionBoundary

bidiNamingCannotRepairLoss :
  BidirectionalSatelliteCorrectionBoundary.correctedNamingAloneRepairsInformationLoss
    canonicalBidirectionalSatelliteCorrectionBoundary ≡ false
bidiNamingCannotRepairLoss =
  BidirectionalSatelliteCorrectionBoundary.correctedNamingAloneRepairsInformationLossIsFalse
    canonicalBidirectionalSatelliteCorrectionBoundary

-- Existing substantive sockets remain part of the same correction surface.
brainStillNeedsMeasurementClosure :
  HemibrainMeasurementClosesPrediction → HemibrainMeasurementClosesPrediction
brainStillNeedsMeasurementClosure receipt = receipt

quantumDiscriminatorSocketPresent :
  ∀ {Theory Experiment Observation : Set}
    {language : DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact.Language Experiment}
    {predicts : DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact.Predictions Theory Experiment Observation}
    {left right : Theory} →
  FalsifiableQuantumTarget language predicts left right →
  ¬ (DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact.EquivalentOn language predicts left right)
quantumDiscriminatorSocketPresent = falsifiableTargetRefutesCurrentEquivalence
