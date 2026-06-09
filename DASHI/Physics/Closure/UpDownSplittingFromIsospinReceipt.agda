module DASHI.Physics.Closure.UpDownSplittingFromIsospinReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Up/down and charged/neutral splitting from the SU(2) doublet.
--
-- This receipt is a count-level structural receipt.  It records the carrier
-- interpretation that a single Heegner lane becomes a two-state matter lane
-- only after dressing by the SU(2)_1 WZW j=1/2 primary.  It does not promote
-- a physical Standard Model reconstruction or DHR gauge equivalence.

data IsospinDoubletState : Set where
  j3PlusHalf :
    IsospinDoubletState

  j3MinusHalf :
    IsospinDoubletState

canonicalIsospinDoubletStates :
  List IsospinDoubletState
canonicalIsospinDoubletStates =
  j3PlusHalf
  ∷ j3MinusHalf
  ∷ []

data LaneSplittingReading : Set where
  quarkLaneGivesUpAndDown :
    LaneSplittingReading

  leptonLaneGivesNeutralAndCharged :
    LaneSplittingReading

  splittingRequiresSU2Dressing :
    LaneSplittingReading

canonicalLaneSplittingReadings :
  List LaneSplittingReading
canonicalLaneSplittingReadings =
  quarkLaneGivesUpAndDown
  ∷ leptonLaneGivesNeutralAndCharged
  ∷ splittingRequiresSU2Dressing
  ∷ []

data UpDownSplittingPromotion : Set where

upDownSplittingPromotionImpossibleHere :
  UpDownSplittingPromotion →
  ⊥
upDownSplittingPromotionImpossibleHere ()

upDownSplittingStatement : String
upDownSplittingStatement =
  "Each carrier quark/lepton lane is dressed by the SU(2)_1 WZW j=1/2 primary: j3=+1/2 and j3=-1/2 give up/down or charged/neutral splitting and supply count-level flavor doubling; this is structural only, not an SM promotion."

record UpDownSplittingFromIsospinReceipt : Setω where
  field
    su2LevelOneBoundaryPrimary :
      Bool

    su2LevelOneBoundaryPrimaryIsTrue :
      su2LevelOneBoundaryPrimary ≡ true

    wzwJHalfPrimaryRecorded :
      Bool

    wzwJHalfPrimaryRecordedIsTrue :
      wzwJHalfPrimaryRecorded ≡ true

    doubletStates :
      List IsospinDoubletState

    doubletStatesAreCanonical :
      doubletStates ≡ canonicalIsospinDoubletStates

    quarkLaneSplitsIntoUpDown :
      Bool

    quarkLaneSplitsIntoUpDownIsTrue :
      quarkLaneSplitsIntoUpDown ≡ true

    leptonLaneSplitsIntoNeutralCharged :
      Bool

    leptonLaneSplitsIntoNeutralChargedIsTrue :
      leptonLaneSplitsIntoNeutralCharged ≡ true

    fermionDoublingFromSU2Primary :
      Bool

    fermionDoublingFromSU2PrimaryIsTrue :
      fermionDoublingFromSU2Primary ≡ true

    readings :
      List LaneSplittingReading

    readingsAreCanonical :
      readings ≡ canonicalLaneSplittingReadings

    exactSU2LGaugeTheoryPromoted :
      Bool

    exactSU2LGaugeTheoryPromotedIsFalse :
      exactSU2LGaugeTheoryPromoted ≡ false

    exactSMFermionRepresentationPromoted :
      Bool

    exactSMFermionRepresentationPromotedIsFalse :
      exactSMFermionRepresentationPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List UpDownSplittingPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ upDownSplittingStatement

open UpDownSplittingFromIsospinReceipt public

canonicalUpDownSplittingFromIsospinReceipt :
  UpDownSplittingFromIsospinReceipt
canonicalUpDownSplittingFromIsospinReceipt =
  record
    { su2LevelOneBoundaryPrimary =
        true
    ; su2LevelOneBoundaryPrimaryIsTrue =
        refl
    ; wzwJHalfPrimaryRecorded =
        true
    ; wzwJHalfPrimaryRecordedIsTrue =
        refl
    ; doubletStates =
        canonicalIsospinDoubletStates
    ; doubletStatesAreCanonical =
        refl
    ; quarkLaneSplitsIntoUpDown =
        true
    ; quarkLaneSplitsIntoUpDownIsTrue =
        refl
    ; leptonLaneSplitsIntoNeutralCharged =
        true
    ; leptonLaneSplitsIntoNeutralChargedIsTrue =
        refl
    ; fermionDoublingFromSU2Primary =
        true
    ; fermionDoublingFromSU2PrimaryIsTrue =
        refl
    ; readings =
        canonicalLaneSplittingReadings
    ; readingsAreCanonical =
        refl
    ; exactSU2LGaugeTheoryPromoted =
        false
    ; exactSU2LGaugeTheoryPromotedIsFalse =
        refl
    ; exactSMFermionRepresentationPromoted =
        false
    ; exactSMFermionRepresentationPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
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
        upDownSplittingStatement
    ; statementIsCanonical =
        refl
    }

upDownSplittingFromIsospinInhabited :
  quarkLaneSplitsIntoUpDown canonicalUpDownSplittingFromIsospinReceipt
  ≡
  true
upDownSplittingFromIsospinInhabited =
  quarkLaneSplitsIntoUpDownIsTrue
    canonicalUpDownSplittingFromIsospinReceipt

fermionDoublingFromSU2PrimaryInhabited :
  fermionDoublingFromSU2Primary canonicalUpDownSplittingFromIsospinReceipt
  ≡
  true
fermionDoublingFromSU2PrimaryInhabited =
  fermionDoublingFromSU2PrimaryIsTrue
    canonicalUpDownSplittingFromIsospinReceipt

upDownSplittingNoClayPromotion :
  clayPromoted canonicalUpDownSplittingFromIsospinReceipt
  ≡
  false
upDownSplittingNoClayPromotion =
  clayPromotedIsFalse
    canonicalUpDownSplittingFromIsospinReceipt

upDownSplittingNoTerminalPromotion :
  terminalClaimPromoted canonicalUpDownSplittingFromIsospinReceipt
  ≡
  false
upDownSplittingNoTerminalPromotion =
  terminalClaimPromotedIsFalse
    canonicalUpDownSplittingFromIsospinReceipt
