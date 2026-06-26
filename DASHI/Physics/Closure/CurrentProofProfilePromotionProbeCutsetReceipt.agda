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
-- is fixed, ymCandidateCompleteNow is now recorded true at the root profile,
-- and the interpretation remains fail-closed because no promotion token is
-- introduced by this probe.

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
  "Fail-closed root probe: the canonical current proof profile records ymCandidateCompleteNow as true, but the probe introduces no promotion token."

record CurrentProofProfilePromotionProbeCutsetReceipt : Setω where
  field
    status :
      CurrentProofProfilePromotionProbeCutsetStatus

    statusIsFailClosed :
      status ≡ rootProbeBlockerCaptured

    rootReceipt :
      Root.CurrentProofProfileReceipt

    rootCandidateCompleteTrue :
      Root.ymCandidateCompleteNow rootReceipt ≡ true

    probePath :
      String

    probePathIsCanonical :
      probePath ≡ currentProofProfilePromotionProbePath

    firstBlockerName :
      String

    firstBlockerNameIsCanonical :
      firstBlockerName ≡ currentProofProfilePromotionProbeFirstBlockerName

    firstBlockerRecordedAsTrue :
      Bool

    firstBlockerRecordedAsTrueIsTrue :
      firstBlockerRecordedAsTrue ≡ true

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
      ∷ "Interpretation: fail-closed because no promotion token is introduced even though ymCandidateCompleteNow is true"
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
    ; rootCandidateCompleteTrue =
        refl
    ; probePath =
        currentProofProfilePromotionProbePath
    ; probePathIsCanonical =
        refl
    ; firstBlockerName =
        currentProofProfilePromotionProbeFirstBlockerName
    ; firstBlockerNameIsCanonical =
        refl
    ; firstBlockerRecordedAsTrue =
        true
    ; firstBlockerRecordedAsTrueIsTrue =
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
        ∷ "Interpretation: fail-closed because no promotion token is introduced even though ymCandidateCompleteNow is true"
        ∷ "No promotion token is introduced"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    }

currentProofProfilePromotionProbeCutsetRecordsRootTrue :
  Root.ymCandidateCompleteNow
    (rootReceipt canonicalCurrentProofProfilePromotionProbeCutsetReceipt)
  ≡
  true
currentProofProfilePromotionProbeCutsetRecordsRootTrue =
  refl

currentProofProfilePromotionProbeCutsetNoPromotion :
  CurrentProofProfilePromotionProbeCutsetPromotion →
  ⊥
currentProofProfilePromotionProbeCutsetNoPromotion =
  currentProofProfilePromotionProbeCutsetPromotionImpossibleHere
