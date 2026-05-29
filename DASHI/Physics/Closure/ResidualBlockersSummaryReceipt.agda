module DASHI.Physics.Closure.ResidualBlockersSummaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- End-of-phase residual blocker summary.

data TractableNextSessionBlocker : Set where
  rrPhiY13Derivation :
    TractableNextSessionBlocker

  waveletMutualCoherenceAndFrameBounds :
    TractableNextSessionBlocker

  su2Level4J2Identification :
    TractableNextSessionBlocker

  csLevelVsSMLevelMismatch :
    TractableNextSessionBlocker

  fourthGenerationMassHierarchyContradiction :
    TractableNextSessionBlocker

canonicalTractableNextSessionBlockers :
  List TractableNextSessionBlocker
canonicalTractableNextSessionBlockers =
  rrPhiY13Derivation
  ∷ waveletMutualCoherenceAndFrameBounds
  ∷ su2Level4J2Identification
  ∷ csLevelVsSMLevelMismatch
  ∷ fourthGenerationMassHierarchyContradiction
  ∷ []

data ExtendedResearchBlocker : Set where
  carrierVEVFromW4HiggsSector :
    ExtendedResearchBlocker

  diracFermionStatisticsFromAnyonicSector :
    ExtendedResearchBlocker

  su3ColourFromCSBulkBoundary :
    ExtendedResearchBlocker

canonicalExtendedResearchBlockers :
  List ExtendedResearchBlocker
canonicalExtendedResearchBlockers =
  carrierVEVFromW4HiggsSector
  ∷ diracFermionStatisticsFromAnyonicSector
  ∷ su3ColourFromCSBulkBoundary
  ∷ []

data ClayWallBlocker : Set where
  continuumRGConvergenceAndScaleAnchoringYM :
    ClayWallBlocker

  bkmEnstrophyControlNS :
    ClayWallBlocker

  fullDHRGaugeGroupEqualsSM :
    ClayWallBlocker

canonicalClayWallBlockers : List ClayWallBlocker
canonicalClayWallBlockers =
  continuumRGConvergenceAndScaleAnchoringYM
  ∷ bkmEnstrophyControlNS
  ∷ fullDHRGaugeGroupEqualsSM
  ∷ []

record ResidualBlockersSummaryReceipt : Setω where
  field
    tractableNextSession :
      List TractableNextSessionBlocker

    tractableNextSessionIsCanonical :
      tractableNextSession ≡ canonicalTractableNextSessionBlockers

    extendedResearch :
      List ExtendedResearchBlocker

    extendedResearchIsCanonical :
      extendedResearch ≡ canonicalExtendedResearchBlockers

    clayWalls :
      List ClayWallBlocker

    clayWallsAreCanonical :
      clayWalls ≡ canonicalClayWallBlockers

    residualBlockerSummaryInhabited :
      Bool

    residualBlockerSummaryInhabitedIsTrue :
      residualBlockerSummaryInhabited ≡ true

    ckmPromotion :
      Bool

    ckmPromotionIsFalse :
      ckmPromotion ≡ false

    smPromotion :
      Bool

    smPromotionIsFalse :
      smPromotion ≡ false

    yangMillsMassGapClayPromoted :
      Bool

    yangMillsMassGapClayPromotedIsFalse :
      yangMillsMassGapClayPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    receiptBoundary :
      List String

open ResidualBlockersSummaryReceipt public

canonicalResidualBlockersSummaryReceipt :
  ResidualBlockersSummaryReceipt
canonicalResidualBlockersSummaryReceipt =
  record
    { tractableNextSession =
        canonicalTractableNextSessionBlockers
    ; tractableNextSessionIsCanonical =
        refl
    ; extendedResearch =
        canonicalExtendedResearchBlockers
    ; extendedResearchIsCanonical =
        refl
    ; clayWalls =
        canonicalClayWallBlockers
    ; clayWallsAreCanonical =
        refl
    ; residualBlockerSummaryInhabited =
        true
    ; residualBlockerSummaryInhabitedIsTrue =
        refl
    ; ckmPromotion =
        false
    ; ckmPromotionIsFalse =
        refl
    ; smPromotion =
        false
    ; smPromotionIsFalse =
        refl
    ; yangMillsMassGapClayPromoted =
        false
    ; yangMillsMassGapClayPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The residual blockers are sorted into tractable, extended-research, and Clay-wall tiers"
        ∷ "Finite scale-zero and scale-one wavelet cancellations do not close the all-scale frame-bound route"
        ∷ "No CKM, SM, YM Clay, NS Clay, or terminal claim is promoted"
        ∷ []
    }

residualBlockersSummaryKeepsTerminalFalse :
  terminalClaimPromoted canonicalResidualBlockersSummaryReceipt ≡ false
residualBlockersSummaryKeepsTerminalFalse =
  refl
