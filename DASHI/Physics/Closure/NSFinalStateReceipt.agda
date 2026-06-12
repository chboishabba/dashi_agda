module DASHI.Physics.Closure.NSFinalStateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayNSCurrentStateReceipt as Current
import DASHI.Physics.Closure.NSLittlewoodPaleyCarrierReceipt as LP
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap
import DASHI.Physics.Closure.NSRegularityRoadmapFilledReceipt as Roadmap
import DASHI.Physics.Closure.NSWaveletRouteClosedReceipt as Wavelet
import DASHI.Physics.Closure.NSWeakSolutionSummaryReceipt as Weak
import DASHI.Physics.Closure.Phase2ProgrammeReceipt as Phase2

------------------------------------------------------------------------
-- Navier-Stokes final-state receipt.

data NSFinalStateStatus : Set where
  candidatePackageConsumedPromotionEvidenceOpen :
    NSFinalStateStatus

data NSFinalStateClosedItem : Set where
  lerayW1EnergyComplete :
    NSFinalStateClosedItem

  lerayW2CompactnessComplete :
    NSFinalStateClosedItem

  lerayW3NonlinearPassageComplete :
    NSFinalStateClosedItem

  lerayW4WeakFormulationComplete :
    NSFinalStateClosedItem

  lerayW5ChainComplete :
    NSFinalStateClosedItem

  twoThreeFiveHaarFrameRouteClosed :
    NSFinalStateClosedItem

  criticalBesovLargeDataRouteClosed :
    NSFinalStateClosedItem

canonicalNSFinalStateClosedItems :
  List NSFinalStateClosedItem
canonicalNSFinalStateClosedItems =
  lerayW1EnergyComplete
  ∷ lerayW2CompactnessComplete
  ∷ lerayW3NonlinearPassageComplete
  ∷ lerayW4WeakFormulationComplete
  ∷ lerayW5ChainComplete
  ∷ twoThreeFiveHaarFrameRouteClosed
  ∷ criticalBesovLargeDataRouteClosed
  ∷ []

data NSFinalStateOpenItem : Set where
  uniformEnstrophyPassageOpen :
    NSFinalStateOpenItem

  uniformVorticityControlOpen :
    NSFinalStateOpenItem

  continuumBKMRegularityPassageOpen :
    NSFinalStateOpenItem

  globalSmoothRegularityOpen :
    NSFinalStateOpenItem

  clayNavierStokesOpen :
    NSFinalStateOpenItem

canonicalNSFinalStateOpenItems :
  List NSFinalStateOpenItem
canonicalNSFinalStateOpenItems =
  uniformEnstrophyPassageOpen
  ∷ uniformVorticityControlOpen
  ∷ continuumBKMRegularityPassageOpen
  ∷ globalSmoothRegularityOpen
  ∷ clayNavierStokesOpen
  ∷ []

data NSFinalStatePromotion : Set where

nsFinalStatePromotionImpossibleHere :
  NSFinalStatePromotion →
  ⊥
nsFinalStatePromotionImpossibleHere ()

nsFinalStateStatement : String
nsFinalStateStatement =
  "NS final state: Leray W1-W5 and the candidate-complete self-contained A1-A9 package are explicit at receipt scope, the classical theorem intake is explicit, and the remaining issue is exact acceptance/promotion of the consumed norms/constants package into continuum enstrophy, BKM regularity, global smoothness, and Clay closure; all promotion flags remain false."

record NSFinalStateReceipt : Setω where
  field
    status :
      NSFinalStateStatus

    weakSummaryReceipt :
      Weak.NSWeakSolutionSummaryReceipt

    w1Complete :
      Weak.w1EnergyInequalityInhabited weakSummaryReceipt ≡ true

    w2Complete :
      Weak.w2CompactnessInhabited weakSummaryReceipt ≡ true

    w3Complete :
      Weak.w3NonlinearPassageInhabited weakSummaryReceipt ≡ true

    w4Complete :
      Weak.w4WeakFormulationInhabited weakSummaryReceipt ≡ true

    w5Complete :
      Weak.w5LerayChainInhabited weakSummaryReceipt ≡ true

    weakSummaryClayFalse :
      Weak.clayNavierStokesPromoted weakSummaryReceipt ≡ false

    waveletRouteReceipt :
      Wavelet.NSWaveletRouteClosedReceipt

    haarFrameRouteClosed :
      Wavelet.nsWaveletRouteFullyClosed waveletRouteReceipt ≡ true

    waveletRouteClayFalse :
      Wavelet.clayNavierStokesPromoted waveletRouteReceipt ≡ false

    littlewoodPaleyReceipt :
      LP.NSLittlewoodPaleyCarrierReceipt

    lpCandidateRecorded :
      LP.carrierLPDecompositionDefined littlewoodPaleyReceipt ≡ true

    lpParaproductBoundFalse :
      LP.paraproductBoundProved littlewoodPaleyReceipt ≡ false

    regularityGapReceipt :
      Gap.NSRegularityGapReceipt

    enstrophyAndVorticityRungsRecorded :
      Gap.finiteDepthRegularityRungsRecorded regularityGapReceipt ≡ true

    regularityGapStillOpen :
      Gap.globalSmoothRegularityProved regularityGapReceipt ≡ false

    bkmVorticityStillOpen :
      Gap.bkmVorticityControlClosed regularityGapReceipt ≡ false

    roadmapReceipt :
      Roadmap.NSRegularityRoadmapFilledReceipt

    roadmapFilled :
      Roadmap.roadmapFilled roadmapReceipt ≡ true

    roadmapVorticityStillOpen :
      Roadmap.vorticityControlClosed roadmapReceipt ≡ false

    currentStateReceipt :
      Current.ClayNSCurrentStateReceipt

    currentLerayTrue :
      Current.lerayWeakSolutionBranchAvailable currentStateReceipt ≡ true

    currentClayFalse :
      Current.clayNavierStokesPromoted currentStateReceipt ≡ false

    phase2Receipt :
      Phase2.Phase2ProgrammeReceipt

    criticalBesovControlNotConstructed :
      Phase2.criticalBesovControlConstructed phase2Receipt ≡ false

    closedItems :
      List NSFinalStateClosedItem

    closedItemsAreCanonical :
      closedItems ≡ canonicalNSFinalStateClosedItems

    openItems :
      List NSFinalStateOpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalNSFinalStateOpenItems

    lerayW1W5Complete :
      Bool

    lerayW1W5CompleteIsTrue :
      lerayW1W5Complete ≡ true

    twoThreeFiveHaarFrameRouteClosedFlag :
      Bool

    twoThreeFiveHaarFrameRouteClosedFlagIsTrue :
      twoThreeFiveHaarFrameRouteClosedFlag ≡ true

    criticalBesovLargeDataRouteClosedFlag :
      Bool

    criticalBesovLargeDataRouteClosedFlagIsTrue :
      criticalBesovLargeDataRouteClosedFlag ≡ true

    enstrophyPassageClosed :
      Bool

    enstrophyPassageClosedIsFalse :
      enstrophyPassageClosed ≡ false

    vorticityControlClosed :
      Bool

    vorticityControlClosedIsFalse :
      vorticityControlClosed ≡ false

    lInfinityVorticityControlClosed :
      Bool

    lInfinityVorticityControlClosedIsFalse :
      lInfinityVorticityControlClosed ≡ false

    globalRegularityClosed :
      Bool

    globalRegularityClosedIsFalse :
      globalRegularityClosed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List NSFinalStatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsFinalStateStatement

    receiptBoundary :
      List String

open NSFinalStateReceipt public

canonicalNSFinalStateReceipt :
  NSFinalStateReceipt
canonicalNSFinalStateReceipt =
  record
    { status =
        candidatePackageConsumedPromotionEvidenceOpen
    ; weakSummaryReceipt =
        Weak.canonicalNSWeakSolutionSummaryReceipt
    ; w1Complete =
        refl
    ; w2Complete =
        refl
    ; w3Complete =
        refl
    ; w4Complete =
        refl
    ; w5Complete =
        refl
    ; weakSummaryClayFalse =
        refl
    ; waveletRouteReceipt =
        Wavelet.canonicalNSWaveletRouteClosedReceipt
    ; haarFrameRouteClosed =
        refl
    ; waveletRouteClayFalse =
        refl
    ; littlewoodPaleyReceipt =
        LP.canonicalNSLittlewoodPaleyCarrierReceipt
    ; lpCandidateRecorded =
        refl
    ; lpParaproductBoundFalse =
        refl
    ; regularityGapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; enstrophyAndVorticityRungsRecorded =
        refl
    ; regularityGapStillOpen =
        refl
    ; bkmVorticityStillOpen =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalNSRegularityRoadmapFilledReceipt
    ; roadmapFilled =
        refl
    ; roadmapVorticityStillOpen =
        refl
    ; currentStateReceipt =
        Current.canonicalClayNSCurrentStateReceipt
    ; currentLerayTrue =
        refl
    ; currentClayFalse =
        refl
    ; phase2Receipt =
        Phase2.canonicalPhase2ProgrammeReceipt
    ; criticalBesovControlNotConstructed =
        refl
    ; closedItems =
        canonicalNSFinalStateClosedItems
    ; closedItemsAreCanonical =
        refl
    ; openItems =
        canonicalNSFinalStateOpenItems
    ; openItemsAreCanonical =
        refl
    ; lerayW1W5Complete =
        true
    ; lerayW1W5CompleteIsTrue =
        refl
    ; twoThreeFiveHaarFrameRouteClosedFlag =
        true
    ; twoThreeFiveHaarFrameRouteClosedFlagIsTrue =
        refl
    ; criticalBesovLargeDataRouteClosedFlag =
        true
    ; criticalBesovLargeDataRouteClosedFlagIsTrue =
        refl
    ; enstrophyPassageClosed =
        false
    ; enstrophyPassageClosedIsFalse =
        refl
    ; vorticityControlClosed =
        false
    ; vorticityControlClosedIsFalse =
        refl
    ; lInfinityVorticityControlClosed =
        false
    ; lInfinityVorticityControlClosedIsFalse =
        refl
    ; globalRegularityClosed =
        false
    ; globalRegularityClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsFinalStateStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "W1-W5 record the Leray weak-solution chain, and the self-contained candidate A1-A9 package is explicit at receipt scope"
        ∷ "The classical theorem intake is explicit; these receipts are no longer blocked on theorem-shape grammar"
        ∷ "The 2/3/5 Haar-frame route and the critical-Besov large-data route are consumed fail-closed as package evidence and do not by themselves promote Clay NS"
        ∷ "The remaining issue is exact acceptance/promotion of the consumed norms/constants package into continuum enstrophy, L-infinity vorticity control, continuum BKM, and global smooth regularity"
        ∷ "Clay Navier-Stokes and terminal promotion remain false"
        ∷ []
    }

nsFinalStateKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSFinalStateReceipt ≡ false
nsFinalStateKeepsClayFalse =
  refl

nsFinalStateKeepsTerminalFalse :
  terminalClaimPromoted canonicalNSFinalStateReceipt ≡ false
nsFinalStateKeepsTerminalFalse =
  refl

nsFinalStateNoPromotion :
  NSFinalStatePromotion →
  ⊥
nsFinalStateNoPromotion =
  nsFinalStatePromotionImpossibleHere
