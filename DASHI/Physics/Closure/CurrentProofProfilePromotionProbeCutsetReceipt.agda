module DASHI.Physics.Closure.CurrentProofProfilePromotionProbeCutsetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CurrentProofProfileReceipt as Root

------------------------------------------------------------------------
-- Current proof profile promotion probe cutset receipt.
--
-- This receipt records the stable cross-lane root-probe blocker without
-- importing the probe itself.  The root receipt is canonical, the probe path
-- is fixed, the first blocker remains ymCandidateCompleteNow, and the
-- interpretation is fail-closed: the current proof profile is not yet
-- promotable from this probe.

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
  "DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda"

currentProofProfilePromotionProbeFirstBlockerName : String
currentProofProfilePromotionProbeFirstBlockerName =
  "ymCandidateCompleteNow"

currentProofProfilePromotionProbeInterpretation : String
currentProofProfilePromotionProbeInterpretation =
  "Fail-closed root probe: the canonical current proof profile still records ymCandidateCompleteNow as false, so the probe remains blocked and no promotion is introduced."

record CurrentProofProfilePromotionProbeCutsetReceipt : Setω where
  field
    status :
      CurrentProofProfilePromotionProbeCutsetStatus

    statusIsFailClosed :
      status ≡ rootProbeBlockerCaptured

    rootReceipt :
      Root.CurrentProofProfileReceipt

    rootProbeBlockerFalse :
      Root.ymCandidateCompleteNow rootReceipt ≡ false

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
      receiptBoundary ≡
      "Probe path: DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda"
      ∷ "First blocker: ymCandidateCompleteNow"
      ∷ "Interpretation: fail-closed because the canonical root receipt keeps ymCandidateCompleteNow false"
      ∷ "No promotion token is introduced"
      ∷ []

open CurrentProofProfilePromotionProbeCutsetReceipt public

canonicalCurrentProofProfilePromotionProbeCutsetReceipt :
  CurrentProofProfilePromotionProbeCutsetReceipt
canonicalCurrentProofProfilePromotionProbeCutsetReceipt =
  record
    { status =
        rootProbeBlockerCaptured
    ; statusIsFailClosed =
        refl
    ; rootReceipt =
        Root.canonicalCurrentProofProfileReceipt
    ; rootProbeBlockerFalse =
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
        "Probe path: DASHI/Physics/Probes/CurrentProofProfilePromotionProbe.agda"
        ∷ "First blocker: ymCandidateCompleteNow"
        ∷ "Interpretation: fail-closed because the canonical root receipt keeps ymCandidateCompleteNow false"
        ∷ "No promotion token is introduced"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    }

currentProofProfilePromotionProbeCutsetKeepsRootFalse :
  Root.ymCandidateCompleteNow
    (rootReceipt canonicalCurrentProofProfilePromotionProbeCutsetReceipt)
  ≡
  false
currentProofProfilePromotionProbeCutsetKeepsRootFalse =
  refl

currentProofProfilePromotionProbeCutsetNoPromotion :
  CurrentProofProfilePromotionProbeCutsetPromotion →
  ⊥
currentProofProfilePromotionProbeCutsetNoPromotion =
  currentProofProfilePromotionProbeCutsetPromotionImpossibleHere
