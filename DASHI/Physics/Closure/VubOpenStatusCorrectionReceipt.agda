module DASHI.Physics.Closure.VubOpenStatusCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C1: |Vub| open-status correction.
--
-- This receipt supersedes the previous purely-open Vub status.  The
-- alpha1*alpha2 formula is recorded as a candidate prediction, not as a
-- physical CKM promotion.

data VubCorrectedStatus : Set where
  vubCandidateFromUpTypeOneThreeDepth :
    VubCorrectedStatus

data VubCorrectionReason : Set where
  alphaOneAlphaTwoEqualsSqrtMuOverMt :
    VubCorrectionReason

  previousOpenStatusOverstated :
    VubCorrectionReason

  candidateAccuracyFourPointSixteenPercent :
    VubCorrectionReason

canonicalVubCorrectionReasons : List VubCorrectionReason
canonicalVubCorrectionReasons =
  alphaOneAlphaTwoEqualsSqrtMuOverMt
  ∷ previousOpenStatusOverstated
  ∷ candidateAccuracyFourPointSixteenPercent
  ∷ []

vubCandidateFormula : String
vubCandidateFormula =
  "|Vub| = alpha1 * alpha2 = sqrt(m_u/m_t)"

vubCandidateValue : String
vubCandidateValue =
  "0.003537"

vubPDGReferenceValue : String
vubPDGReferenceValue =
  "0.003690"

vubCandidateErrorPercent : String
vubCandidateErrorPercent =
  "4.16%"

data VubCorrectionPromotion : Set where

vubCorrectionPromotionImpossibleHere :
  VubCorrectionPromotion →
  ⊥
vubCorrectionPromotionImpossibleHere ()

record VubOpenStatusCorrectionReceipt : Setω where
  field
    vubStatus :
      VubCorrectedStatus

    vubStatusIsCandidate :
      vubStatus ≡ vubCandidateFromUpTypeOneThreeDepth

    vubStatusLabel :
      String

    vubStatusLabelIsCandidate :
      vubStatusLabel ≡ "candidate (4.16%)"

    vubFormula :
      String

    vubFormulaIsAlphaOneAlphaTwo :
      vubFormula ≡ vubCandidateFormula

    vubValue :
      String

    vubValueIsCanonical :
      vubValue ≡ vubCandidateValue

    vubPDGValue :
      String

    vubPDGValueIsCanonical :
      vubPDGValue ≡ vubPDGReferenceValue

    vubError :
      String

    vubErrorIsCanonical :
      vubError ≡ vubCandidateErrorPercent

    structuralOrigin :
      String

    structuralOriginIsUpTypeDepth :
      structuralOrigin
      ≡
      "up-type 1-3 Yukawa depth separation"

    previousReceiptOverridden :
      Bool

    previousReceiptOverriddenIsTrue :
      previousReceiptOverridden ≡ true

    fullVubPromoted :
      Bool

    fullVubPromotedIsFalse :
      fullVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    correctionReasons :
      List VubCorrectionReason

    correctionReasonsAreCanonical :
      correctionReasons ≡ canonicalVubCorrectionReasons

    promotionFlags :
      List VubCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubOpenStatusCorrectionReceipt public

canonicalVubOpenStatusCorrectionReceipt :
  VubOpenStatusCorrectionReceipt
canonicalVubOpenStatusCorrectionReceipt =
  record
    { vubStatus =
        vubCandidateFromUpTypeOneThreeDepth
    ; vubStatusIsCandidate =
        refl
    ; vubStatusLabel =
        "candidate (4.16%)"
    ; vubStatusLabelIsCandidate =
        refl
    ; vubFormula =
        vubCandidateFormula
    ; vubFormulaIsAlphaOneAlphaTwo =
        refl
    ; vubValue =
        vubCandidateValue
    ; vubValueIsCanonical =
        refl
    ; vubPDGValue =
        vubPDGReferenceValue
    ; vubPDGValueIsCanonical =
        refl
    ; vubError =
        vubCandidateErrorPercent
    ; vubErrorIsCanonical =
        refl
    ; structuralOrigin =
        "up-type 1-3 Yukawa depth separation"
    ; structuralOriginIsUpTypeDepth =
        refl
    ; previousReceiptOverridden =
        true
    ; previousReceiptOverriddenIsTrue =
        refl
    ; fullVubPromoted =
        false
    ; fullVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; correctionReasons =
        canonicalVubCorrectionReasons
    ; correctionReasonsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager C1 corrects the previous Vub-open receipt"
        ∷ "The alpha1*alpha2 value is a candidate prediction at 4.16 percent error"
        ∷ "The correction does not promote physical CKM"
        ∷ []
    }

canonicalVubCorrectionKeepsCKMUnpromoted :
  physicalCKMPromoted canonicalVubOpenStatusCorrectionReceipt ≡ false
canonicalVubCorrectionKeepsCKMUnpromoted =
  refl

canonicalVubCorrectionNoPromotion :
  VubCorrectionPromotion →
  ⊥
canonicalVubCorrectionNoPromotion =
  vubCorrectionPromotionImpossibleHere
