module DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Target
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as ClusterDirect
import DASHI.Analysis.RiemannG2LiteralPhaseDirectClusterResponseExact as PhaseDirect
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as High
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as LiteralKernel
import DASHI.Analysis.RiemannG2FinalNearObserverDescentExact as R1Descent
import DASHI.Analysis.RiemannG2LiteralKernelConcreteCertificateBridgeCompilerExact as R1Certificate
import DASHI.Analysis.RiemannG2FinalCarrierFiniteSumCertificateExact as FinalCert
import DASHI.Analysis.RiemannG2CertifiedNearUpperClusterResponseCompilerExact as Certified
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannAnalyticCoordinateObserverDescentExact as R3Descent
import DASHI.Analysis.RiemannG2VerifiedRegionComplementHighCoverExact as R4Complement
import DASHI.Analysis.RiemannAnalyticCoordinateVerifiedRegionRealizationExact as R3Star
import DASHI.Analysis.RiemannG2ClayTerminalR3StarExact as R3StarClay
import DASHI.Analysis.RiemannAnalyticLocatedVerifiedHeightExact as LocatedR3
import DASHI.Analysis.RiemannG2ClayTerminalLocatedR3StarExact as LocatedClay
import DASHI.Analysis.RiemannPlattTrudgianLocatedHeightArithmeticExact as PTArithmetic
import DASHI.Analysis.RiemannBishopPlattTrudgianLocatedHeightExact as PTBishop
import DASHI.Analysis.RiemannBishopLocatedHeightCarrierExact as BishopHeight
import DASHI.Analysis.RiemannAnalyticLocatedHeightCarrierRealizationExact as MinimalLocated
import DASHI.Analysis.RiemannG2ClayTerminalMinimalLocatedR3StarExact as MinimalLocatedClay
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BishopComplex
import DASHI.Analysis.RiemannBishopAnalyticLocatedHeightAttachmentExact as BishopAttachment
import DASHI.Analysis.RiemannBishopSetoidCriticalLineRefinementExact as BishopCritical
import DASHI.Analysis.RiemannPlattTrudgianSameSubstrateLocatedExact as PTSame
import DASHI.Analysis.RiemannG2ClayTerminalBishopLocatedExact as BishopClay
import DASHI.Analysis.RiemannBishopPositiveHeightSymmetryCutExact as PositiveCut
import DASHI.Analysis.RiemannAnalyticConjugationAuthorityGapExact as ConjGap
import DASHI.Analysis.RiemannG2InverseSquareCoefficientCompositionLeanDonorExact as R2RateLean
import DASHI.Analysis.RiemannG2InverseSquareCoefficientR2TargetExact as R2Rate
import DASHI.Analysis.RiemannG2Vendored8889SourceAuditExact as R28889
import DASHI.Analysis.RiemannG2BaselineExcessR2TargetExact as R2Baseline
import DASHI.Analysis.RiemannG2DisplacementAdaptiveFarShellLeanDonorExact as R2FarAdaptive
import DASHI.Analysis.RiemannG2AdaptiveCutoffCrossingCompatibilityLeanDonorExact as R2CutoffCompat
import DASHI.Analysis.RiemannG2AdaptiveBaselineExcessAcquisitionExact as R2Adaptive
import DASHI.Analysis.RiemannG2ProjectiveJointComplementQuadraticLeanDonorExact as R2Projective
import DASHI.Analysis.RiemannG2FinalEvenConeNearFarLeanDonorExact as R2FinalNearFar
import DASHI.Analysis.RiemannG2CenteredGammaQuadraticLeanDonorExact as R2CenteredGamma
import DASHI.Analysis.RiemannG2SignedCenteredLiteralComplementLeanDonorExact as R2SignedCentered
import DASHI.Analysis.RiemannG2FinalLiteralComplementCenteredExactLeanDonor as R2CenteredExact
import DASHI.Analysis.RiemannG2QuadraticMarginUniformityNoGoLeanDonor as R2UniformNoGo
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative
import DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact as Clay
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Donor
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth

------------------------------------------------------------------------
-- CURRENT DIRECT FRONTIER
--
-- The preferred high route now has one evaluator-independent representation
-- theorem and one primitive strict analytic family. A proof-carrying finite
-- certificate is an optional sufficient producer between those two layers.
------------------------------------------------------------------------

data FrontierCoordinate : Set where
  finalNearLiteralRepresentation : FrontierCoordinate
  proofCarryingFiniteUpperCertificate : FrontierCoordinate
  certifiedEnvelopeBelowActualClusterResponse : FrontierCoordinate
  directLiteralPhaseBelowActualClusterResponse : FrontierCoordinate
  finalClusterBalanceAttachment : FrontierCoordinate
  lowPublishedHeightCarrierTransport : FrontierCoordinate
  verifiedRegionDecidability : FrontierCoordinate
  verifiedRegionOrHighCover : FrontierCoordinate
  constructiveDoubleNegatedRH : FrontierCoordinate
  criticalLinePredicateRefinement : FrontierCoordinate
  quarterPeriodCrossingAdmission : FrontierCoordinate
  intermediateQuantitativeClusterMargin : FrontierCoordinate
  quantitativeClusterMarginLower : FrontierCoordinate
  separateFiniteNearEnvelope : FrontierCoordinate
  separateGammaEnvelope : FrontierCoordinate
  finalBalanceAsAnalyticInput : FrontierCoordinate
  exactExistingScalarDonor : FrontierCoordinate

data FrontierClass : Set where
  analyticWall : FrontierClass
  representationWall : FrontierClass
  certificateProducer : FrontierClass
  logicalCarrierWall : FrontierClass
  existingInterface : FrontierClass
  compilerOutput : FrontierClass
  pruned : FrontierClass
  absentDonor : FrontierClass

frontierClass : FrontierCoordinate -> FrontierClass
frontierClass finalNearLiteralRepresentation = representationWall
frontierClass proofCarryingFiniteUpperCertificate = certificateProducer
frontierClass certifiedEnvelopeBelowActualClusterResponse = analyticWall
frontierClass directLiteralPhaseBelowActualClusterResponse = analyticWall
frontierClass finalClusterBalanceAttachment = representationWall
frontierClass lowPublishedHeightCarrierTransport = representationWall
frontierClass verifiedRegionDecidability = logicalCarrierWall
frontierClass verifiedRegionOrHighCover = compilerOutput
frontierClass constructiveDoubleNegatedRH = compilerOutput
frontierClass criticalLinePredicateRefinement = logicalCarrierWall
frontierClass quarterPeriodCrossingAdmission = existingInterface
frontierClass intermediateQuantitativeClusterMargin = pruned
frontierClass quantitativeClusterMarginLower = pruned
frontierClass separateFiniteNearEnvelope = pruned
frontierClass separateGammaEnvelope = pruned
frontierClass finalBalanceAsAnalyticInput = pruned
frontierClass exactExistingScalarDonor = absentDonor

crossingAdmissionRequired :
  Target.DirectLiteralComplementTargetBoundary.quarterPeriodCrossingAdmissionRequired
    Target.canonicalDirectLiteralComplementTargetBoundary ≡ true
crossingAdmissionRequired = refl

narrowWindowRouteRejected :
  Growth.CutoffGrowthBidiBoundary.narrowFixedCutoffCancellationRoutePruned
    Growth.canonicalCutoffGrowthBidiBoundary ≡ true
narrowWindowRouteRejected = refl

literalKernelIsEvaluatorIndependent :
  LiteralKernel.FinalNearLiteralKernelBoundary.evaluatorRequiredToStateLiteralKernel
    LiteralKernel.canonicalFinalNearLiteralKernelBoundary ≡ false
literalKernelIsEvaluatorIndependent = refl

oneLiteralRepresentationEqualityRemains :
  LiteralKernel.FinalNearLiteralKernelBoundary.oneFinalNearToLiteralSumEqualityRequired
    LiteralKernel.canonicalFinalNearLiteralKernelBoundary ≡ true
oneLiteralRepresentationEqualityRemains = refl

r1EmbeddedFoldIsSameObjectChartWitness :
  R1Descent.FinalNearObserverDescentBoundary.embeddedFoldEqualityIsSameObjectChartWitness
    R1Descent.canonicalFinalNearObserverDescentBoundary ≡ true
r1EmbeddedFoldIsSameObjectChartWitness = refl

r1DirectOffBudgetDescendsThroughEmbeddedFold :
  R1Descent.FinalNearObserverDescentBoundary.directOffBudgetFactorsThroughEmbeddedNearFold
    R1Descent.canonicalFinalNearObserverDescentBoundary ≡ true
r1DirectOffBudgetDescendsThroughEmbeddedFold = refl

r1WholeScalarRealizationNotRequiredByOffBudgetConsumer :
  R1Descent.FinalNearObserverDescentBoundary.wholePoleQuotientScalarRealizationRequiredForOffBudgetConsumer
    R1Descent.canonicalFinalNearObserverDescentBoundary ≡ false
r1WholeScalarRealizationNotRequiredByOffBudgetConsumer = refl

r1CertificateBridgeReusesLiteralKernelRepresentation :
  R1Certificate.LiteralKernelCertificateBridgeBoundary.literalKernelEqualityReused
    R1Certificate.canonicalLiteralKernelCertificateBridgeBoundary ≡ true
r1CertificateBridgeReusesLiteralKernelRepresentation = refl

r1CertificateRouteNeedsOnlyFoldWeldAfterLiteralKernel :
  R1Certificate.LiteralKernelCertificateBridgeBoundary.certificateRouteStillNeedsLiteralFoldToCertifiedFoldWeld
    R1Certificate.canonicalLiteralKernelCertificateBridgeBoundary ≡ true
r1CertificateRouteNeedsOnlyFoldWeldAfterLiteralKernel = refl

literalKernelCompilesExistingObserver :
  LiteralKernel.FinalNearLiteralKernelBoundary.existingFinalObserverModelIsCompilerOutput
    LiteralKernel.canonicalFinalNearLiteralKernelBoundary ≡ true
literalKernelCompilesExistingObserver = refl

certificateNeedsNoSelectedWindow :
  FinalCert.FinalCarrierFiniteSumCertificateBoundary.selectedWeilWindowRequired
    FinalCert.canonicalFinalCarrierFiniteSumCertificateBoundary ≡ false
certificateNeedsNoSelectedWindow = refl

certificateUpperTransportsToFinalNear :
  FinalCert.FinalCarrierFiniteSumCertificateBoundary.orderedUpperCertificateTransportsToFinalNear
    FinalCert.canonicalFinalCarrierFiniteSumCertificateBoundary ≡ true
certificateUpperTransportsToFinalNear = refl

certifiedRouteNeedsNoEvaluatorIndexedKernel :
  Certified.CertifiedNearUpperClusterBoundary.evaluatorIndexedKernelRequired
    Certified.canonicalCertifiedNearUpperClusterBoundary ≡ false
certifiedRouteNeedsNoEvaluatorIndexedKernel = refl

certifiedUpperFeedsCanonicalHighPayment :
  Certified.CertifiedNearUpperClusterBoundary.finiteUpperCertificateCanFeedCanonicalHighPayment
    Certified.canonicalCertifiedNearUpperClusterBoundary ≡ true
certifiedUpperFeedsCanonicalHighPayment = refl

certifiedStrictMarginStillRequired :
  Certified.CertifiedNearUpperClusterBoundary.strictCertifiedEnvelopeBelowClusterStillRequired
    Certified.canonicalCertifiedNearUpperClusterBoundary ≡ true
certifiedStrictMarginStillRequired = refl

intermediateClusterMarginPruned :
  ClusterDirect.DirectClusterResponseBoundary.intermediateQuantitativeClusterMarginRequired
    ClusterDirect.canonicalDirectClusterResponseBoundary ≡ false
intermediateClusterMarginPruned = refl

clusterMarginLowerTheoremPruned :
  ClusterDirect.DirectClusterResponseBoundary.clusterMarginLowerTheoremRequired
    ClusterDirect.canonicalDirectClusterResponseBoundary ≡ false
clusterMarginLowerTheoremPruned = refl

analyticPaymentCannotSeeFinalBalance :
  ClusterDirect.DirectClusterResponseBoundary.analyticPaymentCanAccessFinalBalance
    ClusterDirect.canonicalDirectClusterResponseBoundary ≡ false
analyticPaymentCannotSeeFinalBalance = refl

actualClusterResponseIsSingleHighScalarLeaf :
  ClusterDirect.DirectClusterResponseBoundary.directBudgetBelowClusterResponseIsSingleScalarLeaf
    ClusterDirect.canonicalDirectClusterResponseBoundary ≡ true
actualClusterResponseIsSingleHighScalarLeaf = refl

literalPhaseTargetsActualClusterResponse :
  PhaseDirect.LiteralPhaseDirectClusterBoundary.literalPhaseTheoremTargetsActualClusterResponse
    PhaseDirect.canonicalLiteralPhaseDirectClusterBoundary ≡ true
literalPhaseTargetsActualClusterResponse = refl

uniformHighFamilyMatchesPrizeQuantifier :
  High.UniformLiteralPhaseHighBoundary.literalPhaseTheoremFamilyMatchesPrizeHighQuantifier
    High.canonicalUniformLiteralPhaseHighBoundary ≡ true
uniformHighFamilyMatchesPrizeQuantifier = refl

canonicalLowHasNoSeparateSubsetProof :
  Low.CanonicalLowRegionBoundary.separateLowSubsetVerifiedRegionProofRequired
    Low.canonicalLowRegionBoundary ≡ false
canonicalLowHasNoSeparateSubsetProof = refl

negativeRHCompilerOwned :
  Negative.ConstructiveNegativeRHBoundary.directHighLowRouteCompilesDoubleNegatedRH
    Negative.canonicalConstructiveNegativeRHBoundary ≡ true
negativeRHCompilerOwned = refl

criticalPredicateRefinementCompilesStability :
  Stability.CriticalLineStabilityRefinementBoundary.exactPredicateRefinementPlusStabilityCompilesConsumerReceipt
    Stability.canonicalCriticalLineStabilityRefinementBoundary ≡ true
criticalPredicateRefinementCompilesStability = refl

r3CriticalPredicateDescendsThroughRealPart :
  R3Descent.AnalyticCoordinateObserverDescentBoundary.criticalLinePredicateFactorsThroughRealPart
    R3Descent.canonicalAnalyticCoordinateObserverDescentBoundary ≡ true
r3CriticalPredicateDescendsThroughRealPart = refl

r3VerifiedRegionUsesSameHalfCoordinate :
  R3Descent.AnalyticCoordinateObserverDescentBoundary.verifiedRegionLandsInSameHalfCoordinate
    R3Descent.canonicalAnalyticCoordinateObserverDescentBoundary ≡ true
r3VerifiedRegionUsesSameHalfCoordinate = refl

r3NumericVerifiedHeightStillUnpaid :
  R3Descent.AnalyticCoordinateObserverDescentBoundary.numericVerifiedHeightInterpretationPaidHere
    R3Descent.canonicalAnalyticCoordinateObserverDescentBoundary ≡ false
r3NumericVerifiedHeightStillUnpaid = refl

r4ComplementHighCoverCompilesFromVerifiedRegionDecidability :
  R4Complement.VerifiedRegionComplementHighBoundary.coverCompilesFromVerifiedRegionDecidability
    R4Complement.canonicalVerifiedRegionComplementHighBoundary ≡ true
r4ComplementHighCoverCompilesFromVerifiedRegionDecidability = refl

r4SeparateArbitraryCoverNotRequiredOnComplementRoute :
  R4Complement.VerifiedRegionComplementHighBoundary.separateArbitraryCoverTheoremRequiredOnComplementRoute
    R4Complement.canonicalVerifiedRegionComplementHighBoundary ≡ false
r4SeparateArbitraryCoverNotRequiredOnComplementRoute = refl

r4NumericCarrierDoesNotAutomaticallyDecideVerifiedRegion :
  R4Complement.VerifiedRegionComplementHighBoundary.numericCarrierInterpretationAutomaticallyDecidable
    R4Complement.canonicalVerifiedRegionComplementHighBoundary ≡ false
r4NumericCarrierDoesNotAutomaticallyDecideVerifiedRegion = refl

r3StarAbsorbsVerifiedRegionDecisionIntoCoordinatePackage :
  R3Star.AnalyticCoordinateVerifiedRegionRealizationBoundary.coordinateAndVerifiedRegionDecisionShareOnePackage
    R3Star.canonicalAnalyticCoordinateVerifiedRegionRealizationBoundary ≡ true
r3StarAbsorbsVerifiedRegionDecisionIntoCoordinatePackage = refl

r3StarCompilesCanonicalComplementCover :
  R3Star.AnalyticCoordinateVerifiedRegionRealizationBoundary.complementCoverCompilesFromR3Star
    R3Star.canonicalAnalyticCoordinateVerifiedRegionRealizationBoundary ≡ true
r3StarCompilesCanonicalComplementCover = refl

r3StarStillNeedsActualNumericCarrierRealization :
  R3Star.AnalyticCoordinateVerifiedRegionRealizationBoundary.numericHeightCarrierRealizationStillRequired
    R3Star.canonicalAnalyticCoordinateVerifiedRegionRealizationBoundary ≡ true
r3StarStillNeedsActualNumericCarrierRealization = refl

canonicalTerminalSurfaceNeedsNoPrimitiveArbitraryCover :
  R3StarClay.ClayTerminalR3StarBoundary.arbitraryVerifiedOrHighCoverPrimitiveAtCanonicalTerminalSurface
    R3StarClay.canonicalClayTerminalR3StarBoundary ≡ false
canonicalTerminalSurfaceNeedsNoPrimitiveArbitraryCover = refl

r3StarAndUniformHighProducerCompileRH :
  R3StarClay.ClayTerminalR3StarBoundary.theseInputsCompileRH
    R3StarClay.canonicalClayTerminalR3StarBoundary ≡ true
r3StarAndUniformHighProducerCompileRH = refl

locatedR3NeedsNoExactThresholdDecision :
  LocatedR3.LocatedVerifiedHeightBoundary.exactRealThresholdDecidabilityRequired
    LocatedR3.canonicalLocatedVerifiedHeightBoundary ≡ false
locatedR3NeedsNoExactThresholdDecision = refl

locatedR3CotransitivityConstructsLowHighCover :
  LocatedR3.LocatedVerifiedHeightBoundary.strictOrderCotransitivityConstructsCover
    LocatedR3.canonicalLocatedVerifiedHeightBoundary ≡ true
locatedR3CotransitivityConstructsLowHighCover = refl

locatedR3AllowsConstructiveOverlap :
  LocatedR3.LocatedVerifiedHeightBoundary.lowAndHighMayOverlap
    LocatedR3.canonicalLocatedVerifiedHeightBoundary ≡ true
locatedR3AllowsConstructiveOverlap = refl

locatedTerminalNeedsNoArbitraryCover :
  LocatedClay.ClayTerminalLocatedR3StarBoundary.arbitraryCoverPrimitive
    LocatedClay.canonicalClayTerminalLocatedR3StarBoundary ≡ false
locatedTerminalNeedsNoArbitraryCover = refl

locatedTerminalCompilesRH :
  LocatedClay.ClayTerminalLocatedR3StarBoundary.theseInputsCompileRH
    LocatedClay.canonicalClayTerminalLocatedR3StarBoundary ≡ true
locatedTerminalCompilesRH = refl

ptCandidateHalfStrictlyBelowPublishedHeightChecked :
  PTArithmetic.LocatedHeightArithmeticBoundary.strictRationalWindowChecked
    PTArithmetic.canonicalLocatedHeightArithmeticBoundary ≡ true
ptCandidateHalfStrictlyBelowPublishedHeightChecked = refl

ptThresholdWindowConcreteOnBishop :
  PTBishop.BishopPlattTrudgianLocatedHeightBoundary.concreteOrderedRealThresholdsOwned
    PTBishop.canonicalBishopPlattTrudgianLocatedHeightBoundary ≡ true
ptThresholdWindowConcreteOnBishop = refl

bishopMinimalLocatedHeightCarrierInhabited :
  BishopHeight.BishopLocatedHeightCarrierBoundary.concreteBishopCarrierInhabited
    BishopHeight.canonicalBishopLocatedHeightCarrierBoundary ≡ true
bishopMinimalLocatedHeightCarrierInhabited = refl

minimalLocatedRouteNeedsNoCompleteRealPackage :
  MinimalLocated.AnalyticLocatedHeightCarrierBoundary.fullConstructiveRealPackageRequired
    MinimalLocated.canonicalAnalyticLocatedHeightCarrierBoundary ≡ false
minimalLocatedRouteNeedsNoCompleteRealPackage = refl

minimalLocatedTerminalCompilesRH :
  MinimalLocatedClay.ClayTerminalMinimalLocatedR3StarBoundary.theseInputsCompileRH
    MinimalLocatedClay.canonicalClayTerminalMinimalLocatedR3StarBoundary ≡ true
minimalLocatedTerminalCompilesRH = refl

minimalLocatedTerminalStillNeedsSameCarrierLowTheorem :
  MinimalLocatedClay.ClayTerminalMinimalLocatedR3StarBoundary.sameCarrierLowTheoremStillRequired
    MinimalLocatedClay.canonicalClayTerminalMinimalLocatedR3StarBoundary ≡ true
minimalLocatedTerminalStillNeedsSameCarrierLowTheorem = refl

bishopComplexCarrierMakesRealCarrierConcrete :
  BishopComplex.BishopComplexAnalyticCarrierBoundary.realCarrierConcreteBishop
    BishopComplex.canonicalBishopComplexAnalyticCarrierBoundary ≡ true
bishopComplexCarrierMakesRealCarrierConcrete = refl

wholeBishopCarrierIdentityCompilesHeightAttachment :
  BishopAttachment.BishopAnalyticLocatedHeightAttachmentBoundary.minimalLocatedHeightAttachmentCompiles
    BishopAttachment.canonicalBishopAnalyticLocatedHeightAttachmentBoundary ≡ true
wholeBishopCarrierIdentityCompilesHeightAttachment = refl

bishopSetoidEqualityPaysConstructiveStability :
  BishopCritical.BishopSetoidCriticalLineBoundary.bishopSetoidEqualityStableConstructively
    BishopCritical.canonicalBishopSetoidCriticalLineBoundary ≡ true
bishopSetoidEqualityPaysConstructiveStability = refl

agdaRecordEqualityRejectedAsRealEquality :
  BishopCritical.BishopSetoidCriticalLineBoundary.agdaRecordEqualityUsedAsRealEquality
    BishopCritical.canonicalBishopSetoidCriticalLineBoundary ≡ false
agdaRecordEqualityRejectedAsRealEquality = refl

ptSameSubstrateCriticalityIsSingleSourceSeam :
  PTSame.PlattTrudgianSameSubstrateLocatedBoundary.sameSubstrateLowCriticalityIsSingleRemainingSourceTheorem
    PTSame.canonicalPlattTrudgianSameSubstrateLocatedBoundary ≡ true
ptSameSubstrateCriticalityIsSingleSourceSeam = refl

bishopNativeTerminalNeedsNoExactDecision :
  BishopClay.ClayTerminalBishopLocatedBoundary.exactVerifiedRegionDecisionRequired
    BishopClay.canonicalClayTerminalBishopLocatedBoundary ≡ false
bishopNativeTerminalNeedsNoExactDecision = refl

bishopNativeTerminalCompilesRH :
  BishopClay.ClayTerminalBishopLocatedBoundary.theseInputsCompileRH
    BishopClay.canonicalClayTerminalBishopLocatedBoundary ≡ true
bishopNativeTerminalCompilesRH = refl

positiveHeightRouteNeedsNoClassicalSignDecision :
  PositiveCut.BishopPositiveHeightSymmetryCutBoundary.classicalSignDecisionRequired
    PositiveCut.canonicalBishopPositiveHeightSymmetryCutBoundary ≡ false
positiveHeightRouteNeedsNoClassicalSignDecision = refl

positiveHeightRouteNeedsNonzeroSignedOrdinate :
  PositiveCut.BishopPositiveHeightSymmetryCutBoundary.nonzeroSignedOrdinateTheoremRequired
    PositiveCut.canonicalBishopPositiveHeightSymmetryCutBoundary ≡ true
positiveHeightRouteNeedsNonzeroSignedOrdinate = refl

positiveHeightRouteNeedsZeroConjugation :
  PositiveCut.BishopPositiveHeightSymmetryCutBoundary.conjugateNontrivialZeroTheoremRequired
    PositiveCut.canonicalBishopPositiveHeightSymmetryCutBoundary ≡ true
positiveHeightRouteNeedsZeroConjugation = refl

currentAnalyticSubstrateDoesNotDeriveZeroConjugation :
  ConjGap.AnalyticConjugationAuthorityGapBoundary.nontrivialZeroConjugationDerivableFromCurrentFieldsAlone
    ConjGap.canonicalAnalyticConjugationAuthorityGapBoundary ≡ false
currentAnalyticSubstrateDoesNotDeriveZeroConjugation = refl

olderCompletedZetaSymmetryNeedsSameObjectWeld :
  ConjGap.AnalyticConjugationAuthorityGapBoundary.sameObjectBridgeToOlderPackageStillRequiredForReuse
    ConjGap.canonicalAnalyticConjugationAuthorityGapBoundary ≡ true
olderCompletedZetaSymmetryNeedsSameObjectWeld = refl

r2InverseSquareCoefficientCompositionSourceWritten :
  R2RateLean.R2InverseSquareCoefficientCut.genericCoefficientCompositionSourceWrittenInLean
    R2RateLean.canonicalR2InverseSquareCoefficientCut ≡ true
r2InverseSquareCoefficientCompositionSourceWritten = refl

r2QuarticFarCoefficientIs144A :
  R2RateLean.R2InverseSquareCoefficientCut.quarticFarCoefficientIs144TimesA
    R2RateLean.canonicalR2InverseSquareCoefficientCut ≡ true
r2QuarticFarCoefficientIs144A = refl

r2RateCutLeavesNearAnalytic :
  R2Rate.InverseSquareR2RateBoundary.nearRateStillAnalytic
    R2Rate.canonicalInverseSquareR2RateBoundary ≡ true
r2RateCutLeavesNearAnalytic = refl

r2RateCutLeavesGammaAnalytic :
  R2Rate.InverseSquareR2RateBoundary.gammaRateStillAnalytic
    R2Rate.canonicalInverseSquareR2RateBoundary ≡ true
r2RateCutLeavesGammaAnalytic = refl

r2RateCutLeavesActualClusterLowerAnalytic :
  R2Rate.InverseSquareR2RateBoundary.actualClusterLowerRateStillAnalytic
    R2Rate.canonicalInverseSquareR2RateBoundary ≡ true
r2RateCutLeavesActualClusterLowerAnalytic = refl

r2CoefficientCompositionNeedsReplayNotFreshMath :
  R2Rate.InverseSquareR2RateBoundary.coefficientCompositionNeedsFreshMathematics
    R2Rate.canonicalInverseSquareR2RateBoundary ≡ false
r2CoefficientCompositionNeedsReplayNotFreshMath = refl

vendored8889TheoremBytesLocated :
  R28889.Vendored8889AuditBoundary.theoremBytesLocated
    R28889.canonicalVendored8889AuditBoundary ≡ true
vendored8889TheoremBytesLocated = refl

vendoredClusterLowerNeedsTransportNotFreshDerivation :
  R28889.Vendored8889AuditBoundary.clusterFreshDerivationRequiredBeforeTransport
    R28889.canonicalVendored8889AuditBoundary ≡ false
vendoredClusterLowerNeedsTransportNotFreshDerivation = refl

clusterNaturalScaleUsesBaselineAndHorizontalSquare :
  R28889.Vendored8889AuditBoundary.clusterNaturalScaleUsesBaselineAndHorizontalSquare
    R28889.canonicalVendored8889AuditBoundary ≡ true
clusterNaturalScaleUsesBaselineAndHorizontalSquare = refl

fixedQuarticFarNotUniformAsHorizontalDisplacementVanishes :
  R2FarAdaptive.DisplacementAdaptiveFarShellBoundary.fixedQuarticRateUniformlySufficientAsHorizontalDisplacementTendsToZero
    R2FarAdaptive.canonicalDisplacementAdaptiveFarShellBoundary ≡ false
fixedQuarticFarNotUniformAsHorizontalDisplacementVanishes = refl

adaptiveFarMatchesHorizontalSquareScale :
  R2FarAdaptive.DisplacementAdaptiveFarShellBoundary.adaptiveRateMatchesHorizontalSquareScale
    R2FarAdaptive.canonicalDisplacementAdaptiveFarShellBoundary ≡ true
adaptiveFarMatchesHorizontalSquareScale = refl

baselineExcessIsCanonicalR2AcquisitionShape :
  R2Baseline.BaselineExcessR2Boundary.sharedBaselinePrimitive
    R2Baseline.canonicalBaselineExcessR2Boundary ≡ true
baselineExcessIsCanonicalR2AcquisitionShape = refl

adaptiveCutoffCrossingAndFarAccuracyCompatible :
  R2CutoffCompat.AdaptiveCutoffCrossingBoundary.crossingAndFarAccuracyAsymptoticallyCompatible
    R2CutoffCompat.canonicalAdaptiveCutoffCrossingBoundary ≡ true
adaptiveCutoffCrossingAndFarAccuracyCompatible = refl

adaptiveNaturalCutoffExistenceSourceWritten :
  R2CutoffCompat.AdaptiveCutoffCrossingBoundary.genericNaturalCutoffExistenceSourceWritten
    R2CutoffCompat.canonicalAdaptiveCutoffCrossingBoundary ≡ true
adaptiveNaturalCutoffExistenceSourceWritten = refl

adaptiveExactFinalCarrierCutoffTransportStillOpen :
  R2CutoffCompat.AdaptiveCutoffCrossingBoundary.exactFinalCarrierCutoffTransportPaid
    R2CutoffCompat.canonicalAdaptiveCutoffCrossingBoundary ≡ false
adaptiveExactFinalCarrierCutoffTransportStillOpen = refl

adaptiveCutoffMayEnlargeFiniteNearCarrier :
  R2Adaptive.AdaptiveBaselineExcessBoundary.adaptiveCutoffMayEnlargeFiniteNearCarrier
    R2Adaptive.canonicalAdaptiveBaselineExcessBoundary ≡ true
adaptiveCutoffMayEnlargeFiniteNearCarrier = refl

remainingNearLeafIsUniformSignedFiniteCoreCancellation :
  R2Adaptive.AdaptiveBaselineExcessBoundary.nearLeafIsUniformSignedFiniteCoreCancellation
    R2Adaptive.canonicalAdaptiveBaselineExcessBoundary ≡ true
remainingNearLeafIsUniformSignedFiniteCoreCancellation = refl

remainingGammaLeafIsSharpSameTaperRepair :
  R2Adaptive.AdaptiveBaselineExcessBoundary.gammaLeafIsSharpSameTaperRepair
    R2Adaptive.canonicalAdaptiveBaselineExcessBoundary ≡ true
remainingGammaLeafIsSharpSameTaperRepair = refl

projectiveJointComplementQuadraticDonorSourceWritten :
  R2Projective.ProjectiveJointQuadraticBoundary.jointProjectiveQuadraticCompositionSourceWritten
    R2Projective.canonicalProjectiveJointQuadraticBoundary ≡ true
projectiveJointComplementQuadraticDonorSourceWritten = refl

projectiveJointDonorNeedsFullResponseAndBalanceBridge :
  R2Projective.ProjectiveJointQuadraticBoundary.explicitResponseAndBalanceTransportRequiredForFinalReuse
    R2Projective.canonicalProjectiveJointQuadraticBoundary ≡ true
projectiveJointDonorNeedsFullResponseAndBalanceBridge = refl

projectiveTaperEqualityAloneIsInsufficient :
  R2Projective.ProjectiveJointQuadraticBoundary.taperEqualityAloneSufficesForFinalReuse
    R2Projective.canonicalProjectiveJointQuadraticBoundary ≡ false
projectiveTaperEqualityAloneIsInsufficient = refl

projectiveJointDonorDoesNotAlreadyPayFinalR2 :
  R2Projective.ProjectiveJointQuadraticBoundary.jointDonorAlreadyPaysFinalR2
    R2Projective.canonicalProjectiveJointQuadraticBoundary ≡ false
projectiveJointDonorDoesNotAlreadyPayFinalR2 = refl

finalEvenConeNearFarSplitSourceWritten :
  R2FinalNearFar.FinalEvenConeNearFarDonorBoundary.theoremSourceWritten
    R2FinalNearFar.canonicalFinalEvenConeNearFarDonorBoundary ≡ true
finalEvenConeNearFarSplitSourceWritten = refl

finalEvenConeNearFarUsesFinalConsumer :
  R2FinalNearFar.FinalEvenConeNearFarDonorBoundary.finalUniversalEvenConeConsumerUsed
    R2FinalNearFar.canonicalFinalEvenConeNearFarDonorBoundary ≡ true
finalEvenConeNearFarUsesFinalConsumer = refl

finalNearCoreRemainsSigned :
  R2FinalNearFar.FinalEvenConeNearFarDonorBoundary.finiteNearCoreRemainsSigned
    R2FinalNearFar.canonicalFinalEvenConeNearFarDonorBoundary ≡ true
finalNearCoreRemainsSigned = refl

finalNearFarDoesNotYetPayR1 :
  R2FinalNearFar.FinalEvenConeNearFarDonorBoundary.exactR1NearObserverEqualityPaid
    R2FinalNearFar.canonicalFinalEvenConeNearFarDonorBoundary ≡ false
finalNearFarDoesNotYetPayR1 = refl

centeredGammaStripQuadraticSourceWritten :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.centeredStripConstantQuadraticSourceWritten
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ true
centeredGammaStripQuadraticSourceWritten = refl

centeredFinalComplementQuadraticSourceWritten :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.finalJointOffGammaCorrectionQuadraticSourceWritten
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ true
centeredFinalComplementQuadraticSourceWritten = refl

rawGammaSecondDerivativePenaltyNotIntrinsicToCenteredCorrection :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.rawShrinkingSupportSecondDerivativePenaltyIntrinsicToCorrection
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ false
rawGammaSecondDerivativePenaltyNotIntrinsicToCenteredCorrection = refl

radiusZeroJointBaselineStillOpen :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.radiusZeroJointBaselineStillRequiresIdentification
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ true
radiusZeroJointBaselineStillOpen = refl

finalAbsoluteComplementBudgetReducedToRadiusZeroPlusQuadraticExcess :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.finalAbsoluteBudgetReducedToRadiusZeroPlusQuadraticExcess
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ true
finalAbsoluteComplementBudgetReducedToRadiusZeroPlusQuadraticExcess = refl

radiusZeroAbsoluteComplementBudgetIsSingleExplicitSeam :
  R2CenteredGamma.CenteredGammaQuadraticDonorBoundary.radiusZeroAbsoluteBudgetIsNowExplicitSingleSeam
    R2CenteredGamma.canonicalCenteredGammaQuadraticDonorBoundary ≡ true
radiusZeroAbsoluteComplementBudgetIsSingleExplicitSeam = refl

literalSignedComplementCenteredQuadraticSourceWritten :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.literalFinalComplementDifferenceQuadraticSourceWritten
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ true
literalSignedComplementCenteredQuadraticSourceWritten = refl

literalSignedComplementOneSidedUpperSourceWritten :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.literalFinalComplementOneSidedUpperSourceWritten
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ true
literalSignedComplementOneSidedUpperSourceWritten = refl

absoluteBaselineRouteIsNotCanonicalAfterSignedAudit :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.absoluteBaselineRouteCanonical
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ false
absoluteBaselineRouteIsNotCanonicalAfterSignedAudit = refl

radiusZeroPoleIsNotKilledAutomatically :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.radiusZeroPoleChannelAutomaticallyKilled
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ false
radiusZeroPoleIsNotKilledAutomatically = refl

pinnedComplementDoesNotDirectlyPayRadiusZeroBaseline :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.complementChannelsPinnedDirectlyProvesRadiusZeroBaseline
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ false
pinnedComplementDoesNotDirectlyPayRadiusZeroBaseline = refl

signedBaselineIdentificationStillOpen :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.signedBaselineIdentificationStillRequiredForBranchA
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ true
signedBaselineIdentificationStillOpen = refl

adaptiveNearMayBeRepresentationDebt :
  R2SignedCentered.SignedCenteredLiteralComplementBoundary.adaptiveNearMayRemainRepresentationTransportDebt
    R2SignedCentered.canonicalSignedCenteredLiteralComplementBoundary ≡ true
adaptiveNearMayBeRepresentationDebt = refl

exactLiteralComplementCenteringSourceWritten :
  R2CenteredExact.FinalLiteralComplementCenteredExactBoundary.exactCenteredIdentitySourceWritten
    R2CenteredExact.canonicalFinalLiteralComplementCenteredExactBoundary ≡ true
exactLiteralComplementCenteringSourceWritten = refl

centeredSignStillRequired :
  R2CenteredExact.FinalLiteralComplementCenteredExactBoundary.centeredSignOrExactCancellationStillRequired
    R2CenteredExact.canonicalFinalLiteralComplementCenteredExactBoundary ≡ true
centeredSignStillRequired = refl

positiveEnvelopeAloneNotPrizeFacingClosure :
  R2CenteredExact.FinalLiteralComplementCenteredExactBoundary.positiveEnvelopeAloneIsPrizeFacingClosure
    R2CenteredExact.canonicalFinalLiteralComplementCenteredExactBoundary ≡ false
positiveEnvelopeAloneNotPrizeFacingClosure = refl

fixedPositiveErrorCannotFitUniformASquaredMargin :
  R2UniformNoGo.QuadraticMarginUniformityNoGoBoundary.fixedPositiveErrorCannotFitUniformQuadraticMarginSourceWritten
    R2UniformNoGo.canonicalQuadraticMarginUniformityNoGoBoundary ≡ true
fixedPositiveErrorCannotFitUniformASquaredMargin = refl

positiveAIndependentEnvelopeCannotCloseUniformR2 :
  R2UniformNoGo.QuadraticMarginUniformityNoGoBoundary.positiveAIndependentEnvelopeCanCloseUniformR2
    R2UniformNoGo.canonicalQuadraticMarginUniformityNoGoBoundary ≡ false
positiveAIndependentEnvelopeCannotCloseUniformR2 = refl

noConcreteExactScalarDonorFound :
  Donor.ExistingScalarDonorInventoryBoundary.currentInventoryHasConcreteExactDonor
    Donor.canonicalExistingScalarDonorInventoryBoundary ≡ false
noConcreteExactScalarDonorFound = refl

terminalCompilerOwned :
  Clay.ClayTerminalOneLeafBoundary.theseInputsCompileRiemannHypothesisFor
    Clay.canonicalClayTerminalOneLeafBoundary ≡ true
terminalCompilerOwned = refl

record CurrentDirectOneLeafFrontierBoundary : Set where
  constructor current-direct-one-leaf-frontier-boundary
  field
    oneRepresentationEqualityBeforeDirectAnalysis : Bool
    oneRepresentationEqualityBeforeDirectAnalysisIsTrue :
      oneRepresentationEqualityBeforeDirectAnalysis ≡ true

    evaluatorIndependentKernelOwnedAsInterface : Bool
    evaluatorIndependentKernelOwnedAsInterfaceIsTrue :
      evaluatorIndependentKernelOwnedAsInterface ≡ true

    certifiedFiniteUpperIsValidOptionalProducer : Bool
    certifiedFiniteUpperIsValidOptionalProducerIsTrue :
      certifiedFiniteUpperIsValidOptionalProducer ≡ true

    certifiedRouteStillNeedsStrictClusterResponseMargin : Bool
    certifiedRouteStillNeedsStrictClusterResponseMarginIsTrue :
      certifiedRouteStillNeedsStrictClusterResponseMargin ≡ true

    highSideHasOnePrimitiveScalarAnalyticFamily : Bool
    highSideHasOnePrimitiveScalarAnalyticFamilyIsTrue :
      highSideHasOnePrimitiveScalarAnalyticFamily ≡ true

    highLeafTargetsActualClusterResponse : Bool
    highLeafTargetsActualClusterResponseIsTrue :
      highLeafTargetsActualClusterResponse ≡ true

    intermediateQuantitativeClusterMarginStillPrimitive : Bool
    intermediateQuantitativeClusterMarginStillPrimitiveIsFalse :
      intermediateQuantitativeClusterMarginStillPrimitive ≡ false

    analyticPaymentCanSeeFinalBalance : Bool
    analyticPaymentCanSeeFinalBalanceIsFalse :
      analyticPaymentCanSeeFinalBalance ≡ false

    highLeafMustBeUniformOverArbitraryHighOffLineZeros : Bool
    highLeafMustBeUniformOverArbitraryHighOffLineZerosIsTrue :
      highLeafMustBeUniformOverArbitraryHighOffLineZeros ≡ true

    exactSameObjectHarmonicDonorAlreadyFound : Bool
    exactSameObjectHarmonicDonorAlreadyFoundIsFalse :
      exactSameObjectHarmonicDonorAlreadyFound ≡ false

    doubleNegatedRHIsCompilerOutputBeforeStability : Bool
    doubleNegatedRHIsCompilerOutputBeforeStabilityIsTrue :
      doubleNegatedRHIsCompilerOutputBeforeStability ≡ true

    exactCriticalLinePredicateRefinementStillRequiredForPositiveRH : Bool
    exactCriticalLinePredicateRefinementStillRequiredForPositiveRHIsTrue :
      exactCriticalLinePredicateRefinementStillRequiredForPositiveRH ≡ true

    finalClayCompilerClosed : Bool
    finalClayCompilerClosedIsTrue : finalClayCompilerClosed ≡ true

    exactHeadAgdaKernelValidationOwned : Bool
    exactHeadAgdaKernelValidationOwnedIsFalse :
      exactHeadAgdaKernelValidationOwned ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    firstRepresentationWall : String
    preferredCertifiedAnalyticWall : String
    directAnalyticWall : String
    highestAlphaReading : String

canonicalCurrentDirectOneLeafFrontierBoundary : CurrentDirectOneLeafFrontierBoundary
canonicalCurrentDirectOneLeafFrontierBoundary =
  current-direct-one-leaf-frontier-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Realize the exact universal pole-quotient finite kernel and prove nearResponseAt(chosen crossing J) = finiteNearSum(cellResponse). The checked Lean status owner does not transport this equality into Agda."
    "After a proof-carrying upper certificate nearResponseAt(J) <= U, independently prove cast(U + B_far(J)) + cast(D_Gamma(g_pole)) < cast(ClusterResponse(g_pole))."
    "Alternatively prove directly cast(literalFiniteNearValue + B_far(J)) + cast(D_Gamma(g_pole)) < cast(ClusterResponse(g_pole))."
    "The preferred direct route has one exact fold-level representation seam followed by one strict high analytic family. The observer-descent crosswalk proves that the actual Off budget consumer factors through the embedded certified fold once the same-object equality is supplied, and the optional certificate bridge now reuses the literal-kernel equality plus one literal-fold/certified-fold weld rather than demanding a second nearResponse representation. R3 is one shared realPart observer. The exact-complement Dec(V) route and the full ConstructiveCompleteRealPackage located route remain compatibility paths, but neither is preferred. The minimal route now reconstructs the exact rational window X/2 < T_PT with X=6000000185827 and T_PT=3000175332800, transports that inequality concretely to the pinned Murray--Bishop real carrier, and inhabits a minimal LocatedHeightCarrier using Bishop's fast-corollary-2-17. The terminal RH split therefore needs only abs, strict order, the two concrete thresholds, and locatedness: no reciprocal, rational density, Archimedean ceiling, Cauchy package, exact threshold decision, or arbitrary cover. The preferred low-side route is now Bishop-native. A concrete Bishop complex analytic carrier makes conjugation ordinary and Real definitionally Bishop.ℝ; one whole selected-carrier same-object equality compiles the minimal height attachment. Agda record equality is explicitly rejected as real equality. The refined critical predicate is Bishop setoid equality realPart ~= 1/2, and its double-negation stability is now proved constructively from the decidable rational bounds defining Bishop equality, so the former opaque stability field is paid. The remaining low-side semantic seams are now decomposed further. The whole selected AnalyticSubstrate carrier identity and criticalLine iff Bishop-realPart ~= 1/2 remain same-object/predicate welds. For Platt--Trudgian, the positive-height published theorem is separated from the symmetric absolute-height compiler: Bishop sign apartness and abs/neg order geometry are constructive, so no classical sign decision is needed; the actual analytic debts are (a) prove selected nontrivial zeros have nonzero signed ordinate, and (b) prove the selected completed-zeta nontrivial-zero predicate is preserved by conjugation. The current AnalyticSubstrate cannot derive (b) because its abstract isZero predicate lacks equality transport/conjugate-zero laws; the older CompletedZetaData package owns those laws but requires a same-object bridge before reuse. The high branch is handed directly to the implementation-neutral high producer. The companion dashi_lean4 repository now vendors the exact 8889 theorem bytes. Their natural R2 scale is baseline-relative and vanishes quadratically with horizontal displacement a=Re(rho)-1/2: clusterValue_ge_baseline_add_margin gives baselineCluster + (sqrt(2)/2)*a^2*secondMoment(g) <= actual ClusterResponse. Therefore the earlier absolute cCluster/t^2 acquisition cut is only a coarse sufficient compatibility surface, not canonical. The uniform producer should prove complementBudget <= baselineCluster + E and E < clusterMargin. Fixed J=t^4 gives a far error 144*A/t^2 and is not uniformly sufficient as a->0; companion Lean now proves the adaptive real schedule J=(t/alpha)^4 gives 144*A*alpha^2/t^2. Vendored PoleQuotientGammaBudget.lean also proves the historical epsGamma/gammaConeEnvelope lineage is the exact 8889 Gamma producer and locates its precision loss at stripConst's second-derivative L1 term. Thus current R2 work is now sharper again. Companion Lean source directly decomposes the final universal even-cone Off response into a finite signed near core plus an explicit far remainder tending to zero, without using the projective carrier. Separately, exact centering of the literal Gamma samples with h_r=g(cos(ru)-1), together with new pointwise derivative and L1 estimates, proves stripConst(sampleTest h_r t 0) <= r^2*C_center and hence an O(r^2) centered Gamma correction. The same centering is proved on the final Off response and yields a joint final-carrier Off+Gamma radius correction of O(r^2). Therefore the raw shrinking-support ||k''||_1 loss is not intrinsic to the centered correction. The signed-consumer audit and exact-centering tranche supersede the previous coefficient-envelope reading. The terminal Agda consumer is order-valued; separate absolute channel budgets are not primitive. Companion Lean proves the actual literal signed complement S=Off+Q_Gamma satisfies the exact identity S_g(r)-S_g(0)=S_{h_r}(0) with h_r=g(cos(ru)-1)<=0 for nonnegative g, plus the earlier |S(r)-S(0)|<=r^2*E_center magnitude envelope. A new generic theorem proves that any fixed positive error E independent of horizontal displacement a cannot satisfy E<c*a^2 for every nonzero arbitrarily small a. Therefore further tightening of a positive a-independent centered envelope cannot be the Clay-uniform terminal strategy. The live high analytic leaf is now the sign/exact cancellation of the centered literal complement, or alternatively a proof that the surviving correction itself carries an a^2 factor. Radius zero is still not a free baseline: the pole channel survives there, and complementChannels_pinned is at the selected pole-killing radius and uses the downstream final balance. B0_abs remains only a fallback. The adaptive finite-near estimate is not intrinsic to the whole-response centered theorem and may remain R1/transport debt unless the sign route forces a return to the chosen-cutoff carrier. The exact R1 nearResponse equality and Lean-to-Agda theorem transport remain separate. An alternate donor now composes the vendored determinant-level Off and Gamma projective defects into one O(r^2) joint complement theorem, but it remains strictly donor-only because the rank-two/projective taper is not definitionally the final universal pole-quotient taper; a taper-only equality is insufficient: any competitive reuse must transport the projective response and its balance semantics into the changed final pole-quotient comparison object. The rank-two balanced strict consumer is itself a checked no-go, while the pole-quotient lane is the admissible changed comparison. Exact-head Agda validation is not claimed, and RH is not derived."
