module DASHI.Analysis.RiemannG2CurrentDirectOneLeafFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Target
import DASHI.Analysis.RiemannG2DirectIndependentComplementMarginExact as Margin
import DASHI.Analysis.RiemannG2UniformIndependentComplementHighProducerExact as High
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
-- The near scalar is signed and target-centred; B_far is the already-owned
-- transported far-shell budget.  Gamma is kept literal, so the theorem may use
-- joint zero/Gamma cancellation rather than proving a sharp Gamma envelope in
-- isolation.
--
-- LOW-SIDE REPRESENTATION WALL
--
-- Transport the published Platt--Trudgian verified-height theorem onto the same
-- completed-zeta carrier and prove the chosen Low partition lies in that region.
--
-- After these two families plus the existing Low/High cover and critical-line
-- stability interface, RiemannHypothesisFor is compiler output.
------------------------------------------------------------------------

data FrontierCoordinate : Set where
  highIndependentJointComplementMargin : FrontierCoordinate
  lowPublishedHeightCarrierTransport : FrontierCoordinate
  lowHighCover : FrontierCoordinate
  criticalLineStability : FrontierCoordinate
  quarterPeriodCrossingAdmission : FrontierCoordinate
  checkedFarShellTransport : FrontierCoordinate
  finalScalarOrderTaperClusterAttachment : FrontierCoordinate
  separateFiniteNearEnvelope : FrontierCoordinate
  separateGammaEnvelope : FrontierCoordinate
  consumerAssignedAllowanceLayer : FrontierCoordinate
  determinantDirectPayment : FrontierCoordinate
  exactExistingScalarDonor : FrontierCoordinate
  rebuildFinalContradiction : FrontierCoordinate


data FrontierClass : Set where
  analyticWall : FrontierClass
  representationWall : FrontierClass
  existingInterface : FrontierClass
  compilerOutput : FrontierClass
  pruned : FrontierClass
  absentDonor : FrontierClass

frontierClass : FrontierCoordinate -> FrontierClass
frontierClass highIndependentJointComplementMargin = analyticWall
frontierClass lowPublishedHeightCarrierTransport = representationWall
frontierClass lowHighCover = representationWall
frontierClass criticalLineStability = existingInterface
frontierClass quarterPeriodCrossingAdmission = existingInterface
frontierClass checkedFarShellTransport = representationWall
frontierClass finalScalarOrderTaperClusterAttachment = representationWall
frontierClass separateFiniteNearEnvelope = pruned
frontierClass separateGammaEnvelope = pruned
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

    finalClayCompilerClosed : Bool
    finalClayCompilerClosedIsTrue : finalClayCompilerClosed ≡ true

    exactHeadAgdaKernelValidationOwned : Bool
    exactHeadAgdaKernelValidationOwnedIsFalse :
      exactHeadAgdaKernelValidationOwned ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    firstGenuineWall : String
    highestAlphaReading : String

canonicalCurrentDirectOneLeafFrontierBoundary :
  CurrentDirectOneLeafFrontierBoundary
canonicalCurrentDirectOneLeafFrontierBoundary =
  current-direct-one-leaf-frontier-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "Uniformly for every arbitrary high off-line nontrivial zero on the exact quarter-period crossing pole-quotient taper, independently prove cast(D_near(J)+B_far(J)) + cast(D_Gamma(g_pole)) < cast(M_cluster)."
    "All downstream high-side algebra is compiler output on the direct allowance-free route. The signed finite-near phase and Gamma term are intentionally kept together, permitting joint cancellation that the old separate-budget scheduler forbade. The far shell is already quantitatively controlled and crossing is a necessary admission constraint. Repository donor inventory finds no theorem already inhabiting the exact literal target-centred cancellation carrier. Low ordinates reduce separately to same-completed-zeta transport of the published Platt--Trudgian verified region. Exact-head Agda CI is still unavailable because GitHub Actions has produced no run. RH is not derived."
