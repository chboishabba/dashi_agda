module DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Target
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as NearObserver
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannPlattTrudgianCanonicalLowRegionExact as Low
import DASHI.Analysis.RiemannG2ConstructiveNegativeRHCompletionExact as Negative
import DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact as Clay
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Donor
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth

------------------------------------------------------------------------
-- CURRENT DIRECT ONE-LEAF FRONTIER
--
-- The canonical prize path is now normalized on both ends:
--
--   verified-region transport
--   + verified-region-or-High cover
--   + uniform one-leaf high contradiction
--       -> double-negated RH
--   + exact critical-predicate refinement
--       -> positive RH.
--
-- No arbitrary Low predicate, Low-subset proof, channel allowance, separate
-- near/Gamma envelope, or naked CriticalLineStable premise remains canonical.
------------------------------------------------------------------------

data FrontierCoordinate : Set where
  finalNearLiteralPhaseRealisation : FrontierCoordinate
  highIndependentJointComplementMargin : FrontierCoordinate
  lowPublishedHeightCarrierTransport : FrontierCoordinate
  verifiedRegionOrHighCover : FrontierCoordinate
  constructiveDoubleNegatedRH : FrontierCoordinate
  criticalLinePredicateRefinement : FrontierCoordinate
  quarterPeriodCrossingAdmission : FrontierCoordinate
  checkedFarShellTransport : FrontierCoordinate
  finalScalarOrderTaperClusterAttachment : FrontierCoordinate
  arbitraryLowPredicate : FrontierCoordinate
  separateLowSubsetVerifiedRegionProof : FrontierCoordinate
  separateFiniteNearEnvelope : FrontierCoordinate
  separateGammaEnvelope : FrontierCoordinate
  nakedCriticalLineStability : FrontierCoordinate
  consumerAssignedAllowanceLayer : FrontierCoordinate
  determinantDirectPayment : FrontierCoordinate
  exactExistingScalarDonor : FrontierCoordinate
  rebuildFinalContradiction : FrontierCoordinate


data FrontierClass : Set where
  analyticWall : FrontierClass
  representationWall : FrontierClass
  logicalCarrierWall : FrontierClass
  existingInterface : FrontierClass
  compilerOutput : FrontierClass
  pruned : FrontierClass
  absentDonor : FrontierClass

frontierClass : FrontierCoordinate -> FrontierClass
frontierClass finalNearLiteralPhaseRealisation = representationWall
frontierClass highIndependentJointComplementMargin = analyticWall
frontierClass lowPublishedHeightCarrierTransport = representationWall
frontierClass verifiedRegionOrHighCover = representationWall
frontierClass constructiveDoubleNegatedRH = compilerOutput
frontierClass criticalLinePredicateRefinement = logicalCarrierWall
frontierClass quarterPeriodCrossingAdmission = existingInterface
frontierClass checkedFarShellTransport = representationWall
frontierClass finalScalarOrderTaperClusterAttachment = representationWall
frontierClass arbitraryLowPredicate = pruned
frontierClass separateLowSubsetVerifiedRegionProof = pruned
frontierClass separateFiniteNearEnvelope = pruned
frontierClass separateGammaEnvelope = pruned
frontierClass nakedCriticalLineStability = pruned
frontierClass consumerAssignedAllowanceLayer = pruned
frontierClass determinantDirectPayment = pruned
frontierClass exactExistingScalarDonor = absentDonor
frontierClass rebuildFinalContradiction = compilerOutput

------------------------------------------------------------------------
-- Exact pins.
------------------------------------------------------------------------

crossingAdmissionRequired :
  Target.DirectLiteralComplementTargetBoundary.quarterPeriodCrossingAdmissionRequired
    Target.canonicalDirectLiteralComplementTargetBoundary ≡ true
crossingAdmissionRequired = refl

crossingCutoffSameObjectRequired :
  Target.DirectLiteralComplementTargetBoundary.exactCrossingCutoffIdentifiedWithOffCutoff
    Target.canonicalDirectLiteralComplementTargetBoundary ≡ true
crossingCutoffSameObjectRequired = refl

narrowWindowRouteRejected :
  Growth.CutoffGrowthBidiBoundary.narrowFixedCutoffCancellationRoutePruned
    Growth.canonicalCutoffGrowthBidiBoundary ≡ true
narrowWindowRouteRejected = refl

finalNearPhaseRealisationIsFirstObserverRefinement :
  NearObserver.FinalPoleNearObserverRefinementBoundary.targetRelativePhaseIsFirstMissingCoordinate
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ true
finalNearPhaseRealisationIsFirstObserverRefinement = refl

finalNearLiteralModelDoesNotPayMargin :
  NearObserver.FinalPoleNearObserverRefinementBoundary.literalModelAutomaticallyPaysJointMargin
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
finalNearLiteralModelDoesNotPayMargin = refl

oneHighScalarLeaf :
  Margin.DirectIndependentComplementMarginBoundary.oneIndependentJointMarginIsScalarLeaf
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ true
oneHighScalarLeaf = refl

allowanceLayerNotCanonical :
  Margin.DirectIndependentComplementMarginBoundary.consumerAssignedAllowanceLayerRequired
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ false
allowanceLayerNotCanonical = refl

finalBalanceCannotPayLeaf :
  Margin.DirectIndependentComplementMarginBoundary.finalBalanceMayManufactureJointMargin
    Margin.canonicalDirectIndependentComplementMarginBoundary ≡ false
finalBalanceCannotPayLeaf = refl

uniformHighFamilyStillRequired :
  High.UniformIndependentComplementHighBoundary.arbitraryHighOffLineCaseFamilyStillRequired
    High.canonicalUniformIndependentComplementHighBoundary ≡ true
uniformHighFamilyStillRequired = refl

canonicalLowHasNoSeparateSubsetProof :
  Low.CanonicalLowRegionBoundary.separateLowSubsetVerifiedRegionProofRequired
    Low.canonicalLowRegionBoundary ≡ false
canonicalLowHasNoSeparateSubsetProof = refl

lowExactSameCarrierTheoremStillRequired :
  Low.CanonicalLowRegionBoundary.exactSameCarrierCriticalityTheoremStillRequired
    Low.canonicalLowRegionBoundary ≡ true
lowExactSameCarrierTheoremStillRequired = refl

negativeRHCompilerOwned :
  Negative.ConstructiveNegativeRHBoundary.directHighLowRouteCompilesDoubleNegatedRH
    Negative.canonicalConstructiveNegativeRHBoundary ≡ true
negativeRHCompilerOwned = refl

criticalPredicateRefinementCompilesStability :
  Stability.CriticalLineStabilityRefinementBoundary.exactPredicateRefinementPlusStabilityCompilesConsumerReceipt
    Stability.canonicalCriticalLineStabilityRefinementBoundary ≡ true
criticalPredicateRefinementCompilesStability = refl

actualCriticalPredicateRefinementStillOpen :
  Stability.CriticalLineStabilityRefinementBoundary.canonicalActualZetaPredicateRefinementInhabitedHere
    Stability.canonicalCriticalLineStabilityRefinementBoundary ≡ false
actualCriticalPredicateRefinementStillOpen = refl

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
    highSideHasOnePrimitiveScalarAnalyticFamilyIsTrue :
      highSideHasOnePrimitiveScalarAnalyticFamily ≡ true

    finalNearLiteralPhaseRealisationStillRequiredForPhaseRoute : Bool
    finalNearLiteralPhaseRealisationStillRequiredForPhaseRouteIsTrue :
      finalNearLiteralPhaseRealisationStillRequiredForPhaseRoute ≡ true

    highLeafMustBeUniformOverArbitraryHighOffLineZeros : Bool
    highLeafMustBeUniformOverArbitraryHighOffLineZerosIsTrue :
      highLeafMustBeUniformOverArbitraryHighOffLineZeros ≡ true

    highLeafMayUseNarrowSubcriticalCutoff : Bool
    highLeafMayUseNarrowSubcriticalCutoffIsFalse :
      highLeafMayUseNarrowSubcriticalCutoff ≡ false

    highLeafMayBeDerivedFromFinalClusterBalance : Bool
    highLeafMayBeDerivedFromFinalClusterBalanceIsFalse :
      highLeafMayBeDerivedFromFinalClusterBalance ≡ false

    exactSameObjectHarmonicDonorAlreadyFound : Bool
    exactSameObjectHarmonicDonorAlreadyFoundIsFalse :
      exactSameObjectHarmonicDonorAlreadyFound ≡ false

    arbitraryLowPredicateStillCanonical : Bool
    arbitraryLowPredicateStillCanonicalIsFalse :
      arbitraryLowPredicateStillCanonical ≡ false

    separateLowSubsetProofStillCanonical : Bool
    separateLowSubsetProofStillCanonicalIsFalse :
      separateLowSubsetProofStillCanonical ≡ false

    lowPublishedTheoremNeedsSameCarrierTransport : Bool
    lowPublishedTheoremNeedsSameCarrierTransportIsTrue :
      lowPublishedTheoremNeedsSameCarrierTransport ≡ true

    doubleNegatedRHIsCompilerOutputBeforeStability : Bool
    doubleNegatedRHIsCompilerOutputBeforeStabilityIsTrue :
      doubleNegatedRHIsCompilerOutputBeforeStability ≡ true

    nakedCriticalLineStabilityStillPrimitive : Bool
    nakedCriticalLineStabilityStillPrimitiveIsFalse :
      nakedCriticalLineStabilityStillPrimitive ≡ false

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

    firstObserverRefinement : String
    firstGenuineAnalyticWall : String
    highestAlphaReading : String

canonicalCurrentDirectOneLeafFrontierBoundary :
  CurrentDirectOneLeafFrontierBoundary
canonicalCurrentDirectOneLeafFrontierBoundary =
  current-direct-one-leaf-frontier-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Identify final nearResponseAt(chosen crossing J) proof-relevantly with the literal reflection-paired finite near-zero sum exposing target-relative gap, multiplicity and the universal pole-quotient kernel."
    "Uniformly for every arbitrary high off-line nontrivial zero on that exact crossing carrier, independently prove cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster)."
    "The introspective loop now separates observer inadequacy, analytic payment, low-source transport and logical closure. Low is definitionally the verified region, removing an arbitrary partition coordinate and its subset proof. Verified-region transport plus the verified-or-High cover and the uniform high contradiction compile to double-negated RH before any critical-line stability premise. Positive RH then needs only the exact critical-predicate refinement. On the high side, expose the literal target-relative phase hidden by nearResponseAt before reusing phase-sensitive machinery; that refinement does not pay the single uniform joint complement theorem. Exact-head Agda CI remains unavailable and RH is not derived."
