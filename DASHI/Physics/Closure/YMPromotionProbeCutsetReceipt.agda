module DASHI.Physics.Closure.YMPromotionProbeCutsetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed receipt for the current YM root-probe cutset.
--
-- This module records the probe path and the current first blocker name as
-- static receipt data only.  It does not import the probe module itself, so
-- the receipt stays detached from any failing probe surface.

data YMPromotionProbeCutsetStatus : Set where
  ymRootProbeCutsetRecordedFailClosed :
    YMPromotionProbeCutsetStatus

data YMPromotionProbeCutsetBlocker : Set where
  ymL3TightnessConstructed :
    YMPromotionProbeCutsetBlocker

canonicalYMPromotionProbeCutsetBlockers :
  List YMPromotionProbeCutsetBlocker
canonicalYMPromotionProbeCutsetBlockers =
  ymL3TightnessConstructed
  ∷ []

data YMPromotionProbeCutsetPromotion : Set where

ymPromotionProbeCutsetPromotionImpossibleHere :
  YMPromotionProbeCutsetPromotion →
  ⊥
ymPromotionProbeCutsetPromotionImpossibleHere ()

ymPromotionProbePath : String
ymPromotionProbePath =
  "DASHI/Physics/Probes/YMPromotionProbe.agda"

ymPromotionProbeFirstBlockerName : String
ymPromotionProbeFirstBlockerName =
  "ymL3TightnessConstructed"

ymPromotionProbeInterpretation : String
ymPromotionProbeInterpretation =
  "The root YM probe is recorded fail-closed as a static receipt: the probe path is known, the first blocker is ymL3TightnessConstructed, and no probe import or promotion claim is made here."

canonicalYMPromotionProbeCutsetReceiptBoundary :
  List String
canonicalYMPromotionProbeCutsetReceiptBoundary =
  "Probe path recorded without importing the probe module"
  ∷ "Current first blocker name recorded as ymL3TightnessConstructed"
  ∷ "Interpretation remains static and fail-closed"
  ∷ "All promotion claims remain false"
  ∷ []

record YMPromotionProbeCutsetReceipt : Setω where
  field
    status :
      YMPromotionProbeCutsetStatus

    statusIsCanonical :
      status ≡ ymRootProbeCutsetRecordedFailClosed

    probePath :
      String

    probePathIsCanonical :
      probePath ≡ ymPromotionProbePath

    firstBlockerName :
      String

    firstBlockerNameIsCanonical :
      firstBlockerName ≡ ymPromotionProbeFirstBlockerName

    interpretation :
      String

    interpretationIsCanonical :
      interpretation ≡ ymPromotionProbeInterpretation

    probeImportAvoided :
      Bool

    probeImportAvoidedIsTrue :
      probeImportAvoided ≡ true

    probeImportBlocked :
      Bool

    probeImportBlockedIsTrue :
      probeImportBlocked ≡ true

    rootProbeImported :
      Bool

    rootProbeImportedIsFalse :
      rootProbeImported ≡ false

    rootProbePromotionClaimed :
      Bool

    rootProbePromotionClaimedIsFalse :
      rootProbePromotionClaimed ≡ false

    blockers :
      List YMPromotionProbeCutsetBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMPromotionProbeCutsetBlockers

    receiptBoundary :
      List String

    receiptBoundaryAreCanonical :
      receiptBoundary ≡ canonicalYMPromotionProbeCutsetReceiptBoundary

open YMPromotionProbeCutsetReceipt public

canonicalYMPromotionProbeCutsetReceipt :
  YMPromotionProbeCutsetReceipt
canonicalYMPromotionProbeCutsetReceipt =
  record
    { status =
        ymRootProbeCutsetRecordedFailClosed
    ; statusIsCanonical =
        refl
    ; probePath =
        ymPromotionProbePath
    ; probePathIsCanonical =
        refl
    ; firstBlockerName =
        ymPromotionProbeFirstBlockerName
    ; firstBlockerNameIsCanonical =
        refl
    ; interpretation =
        ymPromotionProbeInterpretation
    ; interpretationIsCanonical =
        refl
    ; probeImportAvoided =
        true
    ; probeImportAvoidedIsTrue =
        refl
    ; probeImportBlocked =
        true
    ; probeImportBlockedIsTrue =
        refl
    ; rootProbeImported =
        false
    ; rootProbeImportedIsFalse =
        refl
    ; rootProbePromotionClaimed =
        false
    ; rootProbePromotionClaimedIsFalse =
        refl
    ; blockers =
        canonicalYMPromotionProbeCutsetBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        canonicalYMPromotionProbeCutsetReceiptBoundary
    ; receiptBoundaryAreCanonical =
        refl
    }
