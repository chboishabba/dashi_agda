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

quantumDiscriminatorNotTheory :
  QuantumTargetBoundary.discriminatorAloneIsQuantumGravityTheory
    canonicalQuantumTargetBoundary ≡ false
quantumDiscriminatorNotTheory =
  QuantumTargetBoundary.discriminatorAloneIsQuantumGravityTheoryIsFalse
    canonicalQuantumTargetBoundary

rtxMDLNotPhysicalTruth :
  RTXRefinementBoundary.lowerMDLIsPhysicalTruth
    canonicalRTXRefinementBoundary ≡ false
rtxMDLNotPhysicalTruth =
  RTXRefinementBoundary.lowerMDLIsPhysicalTruthIsFalse
    canonicalRTXRefinementBoundary
