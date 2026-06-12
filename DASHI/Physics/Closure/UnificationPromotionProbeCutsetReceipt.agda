module DASHI.Physics.Closure.UnificationPromotionProbeCutsetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed receipt for the unification promotion root-probe cutset.
--
-- This module records only the static receipt surface: the probe path, the
-- current first blocker name, and a local interpretation.  It does not import
-- the probe itself, so the receipt remains independent of the failing probe
-- module.

data UnificationPromotionProbeCutsetStatus : Set where
  unificationPromotionProbeCutsetRecordedNoPromotion :
    UnificationPromotionProbeCutsetStatus

data UnificationPromotionProbeCutsetPromotion : Set where

unificationPromotionProbeCutsetPromotionImpossibleHere :
  UnificationPromotionProbeCutsetPromotion →
  ⊥
unificationPromotionProbeCutsetPromotionImpossibleHere ()

probePath : String
probePath =
  "DASHI.Physics.Probes.UnificationPromotionProbe"

firstBlockerName : String
firstBlockerName =
  "paper0LaneSpecificAnalyticsProvided"

firstBlockerInterpretation : String
firstBlockerInterpretation =
  "The unification promotion probe is blocked at its first root requirement, so the cutset receipt stays fail-closed and records no promotion."

record UnificationPromotionProbeCutsetReceipt : Setω where
  field
    status :
      UnificationPromotionProbeCutsetStatus

    statusIsFailClosed :
      status ≡ unificationPromotionProbeCutsetRecordedNoPromotion

    probePathRecorded :
      String

    probePathRecordedIsCanonical :
      probePathRecorded ≡ probePath

    firstBlockerNameRecorded :
      String

    firstBlockerNameRecordedIsCanonical :
      firstBlockerNameRecorded ≡ firstBlockerName

    firstBlockerInterpretationRecorded :
      String

    firstBlockerInterpretationRecordedIsCanonical :
      firstBlockerInterpretationRecorded ≡ firstBlockerInterpretation

    probeFailClosed :
      Bool

    probeFailClosedIsTrue :
      probeFailClosed ≡ true

    firstBlockerStillOpen :
      Bool

    firstBlockerStillOpenIsTrue :
      firstBlockerStillOpen ≡ true

    unificationPromotionClaimed :
      Bool

    unificationPromotionClaimedIsFalse :
      unificationPromotionClaimed ≡ false

    promotionFlags :
      List UnificationPromotionProbeCutsetPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open UnificationPromotionProbeCutsetReceipt public

canonicalUnificationPromotionProbeCutsetReceipt :
  UnificationPromotionProbeCutsetReceipt
canonicalUnificationPromotionProbeCutsetReceipt =
  record
    { status =
        unificationPromotionProbeCutsetRecordedNoPromotion
    ; statusIsFailClosed =
        refl
    ; probePathRecorded =
        probePath
    ; probePathRecordedIsCanonical =
        refl
    ; firstBlockerNameRecorded =
        firstBlockerName
    ; firstBlockerNameRecordedIsCanonical =
        refl
    ; firstBlockerInterpretationRecorded =
        firstBlockerInterpretation
    ; firstBlockerInterpretationRecordedIsCanonical =
        refl
    ; probeFailClosed =
        true
    ; probeFailClosedIsTrue =
        refl
    ; firstBlockerStillOpen =
        true
    ; firstBlockerStillOpenIsTrue =
        refl
    ; unificationPromotionClaimed =
        false
    ; unificationPromotionClaimedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Probe path recorded without importing the probe module"
        ∷ "First blocker recorded: paper0LaneSpecificAnalyticsProvided"
        ∷ "Interpretation: fail-closed, no unification promotion claimed"
        ∷ []
    }

unificationPromotionProbeCutsetKeepsPromotionFalse :
  unificationPromotionClaimed canonicalUnificationPromotionProbeCutsetReceipt
  ≡ false
unificationPromotionProbeCutsetKeepsPromotionFalse =
  refl

