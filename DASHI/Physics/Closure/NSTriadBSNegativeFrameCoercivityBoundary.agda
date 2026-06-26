module DASHI.Physics.Closure.NSTriadBSNegativeFrameCoercivityBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only negative-frame coercivity boundary for the corrected
-- positive Wall 1a carrier.
--
-- This is a receipt surface, not a promotion surface.  It records the
-- corrected positive Wall 1a carrier as the negative-frame coercivity
-- statement
--
--   L_neg >= c0 L_abs
--
-- together with the spectral lower bound
--
--   lambda_min(K_N) >= c0 > 0.
--
-- No theorem, Clay, or terminal promotion is introduced here.

negativeFrameCoercivityStatement : String
negativeFrameCoercivityStatement =
  "Corrected positive Wall 1a carrier is recorded as negative-frame coercivity L_neg >= c0 L_abs and lambda_min(K_N) >= c0 > 0."

data NSTriadBSNegativeFrameCoercivityBoundaryStatus : Set where
  candidateOnlyNegativeFrameCoercivityRecorded :
    NSTriadBSNegativeFrameCoercivityBoundaryStatus

data NSTriadBSNegativeFrameCoercivityBoundaryBlocker : Set where
  wall1aCarrierStillCandidateOnly :
    NSTriadBSNegativeFrameCoercivityBoundaryBlocker

  noPromotionFromCoercivityReceipt :
    NSTriadBSNegativeFrameCoercivityBoundaryBlocker

canonicalNSTriadBSNegativeFrameCoercivityBoundaryBlockers :
  List NSTriadBSNegativeFrameCoercivityBoundaryBlocker
canonicalNSTriadBSNegativeFrameCoercivityBoundaryBlockers =
  wall1aCarrierStillCandidateOnly
  ∷ noPromotionFromCoercivityReceipt
  ∷ []

data NSTriadBSNegativeFrameCoercivityBoundaryPromotion : Set where

nSTriadBSNegativeFrameCoercivityBoundaryPromotionImpossibleHere :
  NSTriadBSNegativeFrameCoercivityBoundaryPromotion →
  ⊥
nSTriadBSNegativeFrameCoercivityBoundaryPromotionImpossibleHere ()

record NSTriadBSNegativeFrameCoercivityBoundaryReceipt : Setω where
  field
    status :
      NSTriadBSNegativeFrameCoercivityBoundaryStatus

    statusIsCandidateOnly :
      status ≡ candidateOnlyNegativeFrameCoercivityRecorded

    correctedPositiveWall1aCarrier :
      String

    correctedPositiveWall1aCarrierIsCanonical :
      correctedPositiveWall1aCarrier ≡
      "corrected positive Wall 1a carrier"

    negativeFrameCoercivityStatementField :
      String

    negativeFrameCoercivityStatementFieldIsCanonical :
      negativeFrameCoercivityStatementField ≡
      negativeFrameCoercivityStatement

    L_negGeqC0L_abs :
      Bool

    L_negGeqC0L_absIsTrue :
      L_negGeqC0L_abs ≡ true

    lambdaMinKNGeqC0Positive :
      Bool

    lambdaMinKNGeqC0PositiveIsTrue :
      lambdaMinKNGeqC0Positive ≡ true

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    empiricalNonPromoting :
      Bool

    empiricalNonPromotingIsTrue :
      empiricalNonPromoting ≡ true

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    blockers :
      List NSTriadBSNegativeFrameCoercivityBoundaryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSTriadBSNegativeFrameCoercivityBoundaryBlockers

    promotionFlags :
      List NSTriadBSNegativeFrameCoercivityBoundaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSTriadBSNegativeFrameCoercivityBoundaryReceipt public

canonicalNSTriadBSNegativeFrameCoercivityBoundaryReceipt :
  NSTriadBSNegativeFrameCoercivityBoundaryReceipt
canonicalNSTriadBSNegativeFrameCoercivityBoundaryReceipt =
  record
    { status =
        candidateOnlyNegativeFrameCoercivityRecorded
    ; statusIsCandidateOnly =
        refl
    ; correctedPositiveWall1aCarrier =
        "corrected positive Wall 1a carrier"
    ; correctedPositiveWall1aCarrierIsCanonical =
        refl
    ; negativeFrameCoercivityStatementField =
        negativeFrameCoercivityStatement
    ; negativeFrameCoercivityStatementFieldIsCanonical =
        refl
    ; L_negGeqC0L_abs =
        true
    ; L_negGeqC0L_absIsTrue =
        refl
    ; lambdaMinKNGeqC0Positive =
        true
    ; lambdaMinKNGeqC0PositiveIsTrue =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; empiricalNonPromoting =
        true
    ; empiricalNonPromotingIsTrue =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; blockers =
        canonicalNSTriadBSNegativeFrameCoercivityBoundaryBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The corrected Wall 1a carrier is recorded only as a negative-frame coercivity boundary"
        ∷ "The route remains candidate-only and non-promoting"
        ∷ "No theorem, Clay, or terminal promotion is claimed"
        ∷ []
    }

negativeFrameCoercivityKeepsPromotionFalse :
  theoremPromoted canonicalNSTriadBSNegativeFrameCoercivityBoundaryReceipt ≡ false
negativeFrameCoercivityKeepsPromotionFalse =
  refl
