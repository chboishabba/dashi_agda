module DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Target
import DASHI.Analysis.RiemannG2DirectClusterResponseContradictionExact as ClusterDirect
import DASHI.Analysis.RiemannG2LiteralPhaseDirectClusterResponseExact as PhaseDirect
import DASHI.Analysis.RiemannG2UniformLiteralPhaseHighProducerExact as High
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as NearObserver
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative
import DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact as Clay
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Donor
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth

-- Current canonical high route is literal and balance-free at the analytic leaf.
data FrontierCoordinate : Set where
  finalNearLiteralPhaseRealisation : FrontierCoordinate
  highLiteralPhaseBelowActualClusterResponse : FrontierCoordinate
  finalClusterBalanceAttachment : FrontierCoordinate
  lowPublishedHeightCarrierTransport : FrontierCoordinate
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
  logicalCarrierWall : FrontierClass
  existingInterface : FrontierClass
  compilerOutput : FrontierClass
  pruned : FrontierClass
  absentDonor : FrontierClass

frontierClass : FrontierCoordinate → FrontierClass
frontierClass finalNearLiteralPhaseRealisation = representationWall
frontierClass highLiteralPhaseBelowActualClusterResponse = analyticWall
frontierClass finalClusterBalanceAttachment = representationWall
frontierClass lowPublishedHeightCarrierTransport = representationWall
frontierClass verifiedRegionOrHighCover = representationWall
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

finalNearPhaseRealisationIsFirstObserverRefinement :
  NearObserver.FinalPoleNearObserverRefinementBoundary.targetRelativePhaseIsFirstMissingCoordinate
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ true
finalNearPhaseRealisationIsFirstObserverRefinement = refl

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

literalPhaseHasNoIntermediateMargin :
  PhaseDirect.LiteralPhaseDirectClusterBoundary.intermediateClusterMarginPrimitive
    PhaseDirect.canonicalLiteralPhaseDirectClusterBoundary ≡ false
literalPhaseHasNoIntermediateMargin = refl

uniformHighHasNoIntermediateMargin :
  High.UniformLiteralPhaseHighBoundary.intermediateClusterMarginPrimitivePerCase
    High.canonicalUniformLiteralPhaseHighBoundary ≡ false
uniformHighHasNoIntermediateMargin = refl

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
    highSideHasOnePrimitiveScalarAnalyticFamily : Bool
    highSideHasOnePrimitiveScalarAnalyticFamilyIsTrue : highSideHasOnePrimitiveScalarAnalyticFamily ≡ true
    highLeafTargetsActualClusterResponse : Bool
    highLeafTargetsActualClusterResponseIsTrue : highLeafTargetsActualClusterResponse ≡ true
    intermediateQuantitativeClusterMarginStillPrimitive : Bool
    intermediateQuantitativeClusterMarginStillPrimitiveIsFalse : intermediateQuantitativeClusterMarginStillPrimitive ≡ false
    quantitativeClusterMarginLowerStillPrimitive : Bool
    quantitativeClusterMarginLowerStillPrimitiveIsFalse : quantitativeClusterMarginLowerStillPrimitive ≡ false
    analyticPaymentCanSeeFinalBalance : Bool
    analyticPaymentCanSeeFinalBalanceIsFalse : analyticPaymentCanSeeFinalBalance ≡ false
    highLeafMustBeUniformOverArbitraryHighOffLineZeros : Bool
    highLeafMustBeUniformOverArbitraryHighOffLineZerosIsTrue : highLeafMustBeUniformOverArbitraryHighOffLineZeros ≡ true
    exactSameObjectHarmonicDonorAlreadyFound : Bool
    exactSameObjectHarmonicDonorAlreadyFoundIsFalse : exactSameObjectHarmonicDonorAlreadyFound ≡ false
    doubleNegatedRHIsCompilerOutputBeforeStability : Bool
    doubleNegatedRHIsCompilerOutputBeforeStabilityIsTrue : doubleNegatedRHIsCompilerOutputBeforeStability ≡ true
    exactCriticalLinePredicateRefinementStillRequiredForPositiveRH : Bool
    exactCriticalLinePredicateRefinementStillRequiredForPositiveRHIsTrue : exactCriticalLinePredicateRefinementStillRequiredForPositiveRH ≡ true
    finalClayCompilerClosed : Bool
    finalClayCompilerClosedIsTrue : finalClayCompilerClosed ≡ true
    exactHeadAgdaKernelValidationOwned : Bool
    exactHeadAgdaKernelValidationOwnedIsFalse : exactHeadAgdaKernelValidationOwned ≡ false
    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false
    firstObserverRefinement : String
    firstGenuineAnalyticWall : String
    highestAlphaReading : String

canonicalCurrentDirectOneLeafFrontierBoundary : CurrentDirectOneLeafFrontierBoundary
canonicalCurrentDirectOneLeafFrontierBoundary =
  current-direct-one-leaf-frontier-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Identify final nearResponseAt(chosen crossing J) proof-relevantly with the literal reflection-paired finite near-zero sum exposing the target-relative phase."
    "Uniformly for every arbitrary high off-line nontrivial zero, independently of the final balance, prove cast(literalFiniteNearValue + B_far(J)) + cast(D_Gamma(g_pole)) < cast(ClusterResponse(g_pole))."
    "The high route targets the actual ClusterResponse directly. Intermediate M_cluster and M_cluster<=ClusterResponse are pruned, and cluster=Off+Gamma is downstream only. Low-source transport and critical-predicate refinement remain separate. Exact-head Agda validation is not claimed and RH is not derived."
