module DASHI.Physics.Probes.CurrentProofProfilePromotionProbe where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fail-closed surface for the current proof profile probe.
--
-- This module intentionally stays local to the probe tree.  The closure
-- receipt chain is currently unstable, so the honest aggregate records the
-- probe path and the first blocker directly without importing the closure
-- receipt.

data CurrentProofProfilePromotionProbeCutsetStatus : Set where
  rootProbeBlockerCaptured :
    CurrentProofProfilePromotionProbeCutsetStatus

data CurrentProofProfilePromotionProbeCutsetPromotion : Set where

currentProofProfilePromotionProbeCutsetPromotionImpossibleHere :
  CurrentProofProfilePromotionProbeCutsetPromotion →
  ⊥
currentProofProfilePromotionProbeCutsetPromotionImpossibleHere ()

currentProofProfilePromotionProbePath : String
currentProofProfilePromotionProbePath =
  "DASHI.Physics.Probes.CurrentProofProfilePromotionProbe"

currentProofProfilePromotionProbeFirstBlockerName : String
currentProofProfilePromotionProbeFirstBlockerName =
  "ymCandidateCompleteNow"

currentProofProfilePromotionProbeInterpretation : String
currentProofProfilePromotionProbeInterpretation =
  "Fail-closed root probe: the current proof profile records ymCandidateCompleteNow as blocked, so no promotion token is introduced."

canonicalCurrentProofProfilePromotionProbeCutsetBoundary :
  List String
canonicalCurrentProofProfilePromotionProbeCutsetBoundary =
  "Probe path recorded without importing the closure receipt"
  ∷ "First blocker recorded as ymCandidateCompleteNow"
  ∷ "Interpretation remains fail-closed"
  ∷ "No promotion token is introduced"
  ∷ []

record CurrentProofProfilePromotionProbeCutsetReceipt : Setω where
  field
    status :
      CurrentProofProfilePromotionProbeCutsetStatus

    statusIsFailClosed :
      status ≡ rootProbeBlockerCaptured

    probePath :
      String

    probePathIsCanonical :
      probePath ≡ currentProofProfilePromotionProbePath

    firstBlockerName :
      String

    firstBlockerNameIsCanonical :
      firstBlockerName ≡ currentProofProfilePromotionProbeFirstBlockerName

    firstBlockerRecordedAsFalse :
      Bool

    firstBlockerRecordedAsFalseIsFalse :
      firstBlockerRecordedAsFalse ≡ false

    interpretation :
      String

    interpretationIsCanonical :
      interpretation ≡ currentProofProfilePromotionProbeInterpretation

    promotionFlags :
      List CurrentProofProfilePromotionProbeCutsetPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalCurrentProofProfilePromotionProbeCutsetBoundary

open CurrentProofProfilePromotionProbeCutsetReceipt public

canonicalCurrentProofProfilePromotionProbeCutsetReceipt :
  CurrentProofProfilePromotionProbeCutsetReceipt
canonicalCurrentProofProfilePromotionProbeCutsetReceipt =
  record
    { status =
        rootProbeBlockerCaptured
    ; statusIsFailClosed =
        refl
    ; probePath =
        currentProofProfilePromotionProbePath
    ; probePathIsCanonical =
        refl
    ; firstBlockerName =
        currentProofProfilePromotionProbeFirstBlockerName
    ; firstBlockerNameIsCanonical =
        refl
    ; firstBlockerRecordedAsFalse =
        false
    ; firstBlockerRecordedAsFalseIsFalse =
        refl
    ; interpretation =
        currentProofProfilePromotionProbeInterpretation
    ; interpretationIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalCurrentProofProfilePromotionProbeCutsetBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

currentProofProfilePromotionProbeCutsetNoPromotion :
  CurrentProofProfilePromotionProbeCutsetPromotion →
  ⊥
currentProofProfilePromotionProbeCutsetNoPromotion =
  currentProofProfilePromotionProbeCutsetPromotionImpossibleHere
