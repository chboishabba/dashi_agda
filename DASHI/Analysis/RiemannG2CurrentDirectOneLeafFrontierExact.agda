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
    "The preferred direct route has one exact fold-level representation seam followed by one strict high analytic family. The observer-descent crosswalk proves that the actual Off budget consumer factors through the embedded certified fold once the same-object equality is supplied, and the optional certificate bridge now reuses the literal-kernel equality plus one literal-fold/certified-fold weld rather than demanding a second nearResponse representation. R3 is one shared realPart observer. The exact-complement Dec(V) route and the full ConstructiveCompleteRealPackage located route remain compatibility paths, but neither is preferred. The minimal route now reconstructs the exact rational window X/2 < T_PT with X=6000000185827 and T_PT=3000175332800, transports that inequality concretely to the pinned Murray--Bishop real carrier, and inhabits a minimal LocatedHeightCarrier using Bishop's fast-corollary-2-17. The terminal RH split therefore needs only abs, strict order, the two concrete thresholds, and locatedness: no reciprocal, rational density, Archimedean ceiling, Cauchy package, exact threshold decision, or arbitrary cover. The preferred low-side route is now Bishop-native. A concrete Bishop complex analytic carrier makes conjugation ordinary and Real definitionally Bishop.ℝ; one whole selected-carrier same-object equality compiles the minimal height attachment. Agda record equality is explicitly rejected as real equality. The refined critical predicate is Bishop setoid equality realPart ~= 1/2, and its double-negation stability is now proved constructively from the decidable rational bounds defining Bishop equality, so the former opaque stability field is paid. The remaining low-side semantic seams are only: the whole selected AnalyticSubstrate carrier identity, the exact criticalLine iff Bishop-realPart ~= 1/2 characterization on its completed-zeta predicate, and the same-substrate Platt--Trudgian theorem carrying every located verified zero to that critical predicate (including the positive-to-absolute symmetry transport). The high branch is handed directly to the implementation-neutral high producer. R2 remains the primitive strict ClusterResponse analytic family, exact-head Agda validation is not claimed, and RH is not derived."
