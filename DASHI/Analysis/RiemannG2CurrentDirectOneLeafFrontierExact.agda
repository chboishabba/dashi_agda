module DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Target
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as NearObserver
import DASHI.Analysis.RiemannCriticalLineStabilityRefinementExact as Stability
import DASHI.Analysis.RiemannPlattTrudgianLowCompletionAdapterExact as Low
import DASHI.Analysis.RiemannG2ClayTerminalOneLeafCutExact as Clay
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Donor
import DASHI.Analysis.RiemannG2CutoffGrowthBidiExact as Growth

------------------------------------------------------------------------
-- CURRENT DIRECT ONE-LEAF FRONTIER
--
-- This owner supersedes the older allowance/payment scheduler for proof search.
-- Historical allowance and analytic-core routes remain sufficient interfaces,
-- but they are not prerequisites of the shortest current Clay path.
--
-- INTROSPECTIVE PRECONDITION TO THE HIGH ANALYTIC WALL
--
-- The terminal one-leaf theorem consumes `nearResponseAt J`, but the final
-- transport exposes that object only as a scalar plus an opaque
-- `sameFiniteNearCarrier : Set` receipt.  Existing phase-sensitive machinery
-- needs the target-relative gaps, multiplicities and reflection-paired finite
-- summands.  Therefore the first representation refinement is to identify the
-- exact final near scalar with its literal phase-visible finite sum.
--
-- HIGH-SIDE ANALYTIC WALL
--
-- For every arbitrary high nontrivial zero rho, assuming rho is off the critical
-- line, choose the exact quarter-period crossing cutoff J on the literal
-- pole-quotient taper and prove, independently of the final balance,
--
--   cast(D_near(J) + B_far(J))
--     + cast(D_Gamma(g_pole))
--       < cast(M_cluster).
--
-- LOW-SIDE REPRESENTATION WALL
--
-- Transport the published Platt--Trudgian verified-height theorem onto the same
-- completed-zeta carrier and prove the chosen Low partition lies in that region.
--
-- LOGICAL/CARRIER WALL
--
-- The high contradiction yields double-negated criticality.  Since the current
-- AnalyticSubstrate stores `criticalLine` as an arbitrary predicate, refine that
-- exact predicate to a concrete stable predicate; naked CriticalLineStable is no
-- longer a primitive terminal premise.
------------------------------------------------------------------------

data FrontierCoordinate : Set where
  finalNearLiteralPhaseRealisation : FrontierCoordinate
  highIndependentJointComplementMargin : FrontierCoordinate
  lowPublishedHeightCarrierTransport : FrontierCoordinate
  lowHighCover : FrontierCoordinate
  criticalLinePredicateRefinement : FrontierCoordinate
  quarterPeriodCrossingAdmission : FrontierCoordinate
  checkedFarShellTransport : FrontierCoordinate
  finalScalarOrderTaperClusterAttachment : FrontierCoordinate
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
frontierClass lowHighCover = representationWall
frontierClass criticalLinePredicateRefinement = logicalCarrierWall
frontierClass quarterPeriodCrossingAdmission = existingInterface
frontierClass checkedFarShellTransport = representationWall
frontierClass finalScalarOrderTaperClusterAttachment = representationWall
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

lowCarrierTransportStillRequired :
  Low.PlattTrudgianLowCompletionBoundary.lowPartitionContainmentStillRequiresExactTransport
    Low.canonicalPlattTrudgianLowCompletionBoundary ≡ true
lowCarrierTransportStillRequired = refl

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

    lowPublishedTheoremNeedsCarrierTransport : Bool
    lowPublishedTheoremNeedsCarrierTransportIsTrue :
      lowPublishedTheoremNeedsCarrierTransport ≡ true

    nakedCriticalLineStabilityStillPrimitive : Bool
    nakedCriticalLineStabilityStillPrimitiveIsFalse :
      nakedCriticalLineStabilityStillPrimitive ≡ false

    exactCriticalLinePredicateRefinementStillRequired : Bool
    exactCriticalLinePredicateRefinementStillRequiredIsTrue :
      exactCriticalLinePredicateRefinementStillRequired ≡ true

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
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Identify final nearResponseAt(chosen crossing J) proof-relevantly with the literal reflection-paired finite near-zero sum exposing target-relative gap, multiplicity and the universal pole-quotient kernel."
    "Uniformly for every arbitrary high off-line nontrivial zero on that exact crossing carrier, independently prove cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster)."
    "The introspective loop now separates observer inadequacy from analytic payment. Before reusing phase-sensitive harmonic machinery, expose the literal target-relative phase hidden by the final nearResponseAt scalar. This refinement does not itself pay the joint margin. The only high scalar analytic family remains the independent joint complement inequality; the far shell and quarter-period admission are already controlled/typed. Low ordinates still need same-completed-zeta transport of Platt--Trudgian. The abstract criticalLine predicate also needs an exact stable refinement; the canonical Clay compiler derives CriticalLineStable from that refinement rather than assuming it nakedly. Exact-head Agda CI remains unavailable and RH is not derived."
