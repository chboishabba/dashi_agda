module DASHI.Physics.Closure.NSTriadBSSpanningLemmaReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTriadBSNegativeFrameCoercivityBoundary
  as Boundary

------------------------------------------------------------------------
-- Fail-closed spanning receipt for the negative-frame coercivity lane.
--
-- This module is supporting route material only.  It records the spanning
-- note around rank(B_neg) = rank(B) and keeps the lane candidate-only and
-- non-promoting.

spanningLemmaStatement : String
spanningLemmaStatement =
  "Fail-closed spanning note: rank(B_neg) = rank(B) is recorded as supporting route material, not a promotion."

data NSTriadBSSpanningLemmaReceiptStatus : Set where
  spanningReceiptRecorded :
    NSTriadBSSpanningLemmaReceiptStatus

data NSTriadBSSpanningLemmaReceiptBlocker : Set where
  rankEqualityIsSupportingMaterialOnly :
    NSTriadBSSpanningLemmaReceiptBlocker

  noPromotionFromRankEquality :
    NSTriadBSSpanningLemmaReceiptBlocker

canonicalNSTriadBSSpanningLemmaReceiptBlockers :
  List NSTriadBSSpanningLemmaReceiptBlocker
canonicalNSTriadBSSpanningLemmaReceiptBlockers =
  rankEqualityIsSupportingMaterialOnly
  ∷ noPromotionFromRankEquality
  ∷ []

data NSTriadBSSpanningLemmaReceiptPromotion : Set where

nSTriadBSSpanningLemmaReceiptPromotionImpossibleHere :
  NSTriadBSSpanningLemmaReceiptPromotion →
  ⊥
nSTriadBSSpanningLemmaReceiptPromotionImpossibleHere ()

record NSTriadBSSpanningLemmaReceipt : Setω where
  field
    boundaryReceipt :
      Boundary.NSTriadBSNegativeFrameCoercivityBoundaryReceipt

    boundaryReceiptIsCanonical :
      Bool

    boundaryReceiptIsCanonicalIsTrue :
      boundaryReceiptIsCanonical ≡ true

    status :
      NSTriadBSSpanningLemmaReceiptStatus

    statusIsRecorded :
      status ≡ spanningReceiptRecorded

    rankBNeg :
      String

    rankBNegIsCanonical :
      rankBNeg ≡ "rank(B_neg)"

    rankB :
      String

    rankBIsCanonical :
      rankB ≡ "rank(B)"

    rankEqualityStatement :
      String

    rankEqualityStatementIsCanonical :
      rankEqualityStatement ≡
      spanningLemmaStatement

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

    supportingRouteMaterial :
      Bool

    supportingRouteMaterialIsTrue :
      supportingRouteMaterial ≡ true

    blockers :
      List NSTriadBSSpanningLemmaReceiptBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSTriadBSSpanningLemmaReceiptBlockers

    promotionFlags :
      List NSTriadBSSpanningLemmaReceiptPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSTriadBSSpanningLemmaReceipt public

canonicalNSTriadBSSpanningLemmaReceipt :
  NSTriadBSSpanningLemmaReceipt
canonicalNSTriadBSSpanningLemmaReceipt =
  record
    { boundaryReceipt =
        Boundary.canonicalNSTriadBSNegativeFrameCoercivityBoundaryReceipt
    ; boundaryReceiptIsCanonical =
        true
    ; boundaryReceiptIsCanonicalIsTrue =
        refl
    ; status =
        spanningReceiptRecorded
    ; statusIsRecorded =
        refl
    ; rankBNeg =
        "rank(B_neg)"
    ; rankBNegIsCanonical =
        refl
    ; rankB =
        "rank(B)"
    ; rankBIsCanonical =
        refl
    ; rankEqualityStatement =
        spanningLemmaStatement
    ; rankEqualityStatementIsCanonical =
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
    ; supportingRouteMaterial =
        true
    ; supportingRouteMaterialIsTrue =
        refl
    ; blockers =
        canonicalNSTriadBSSpanningLemmaReceiptBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The rank(B_neg)=rank(B) note is supporting route material only"
        ∷ "The spanning note remains candidate-only and non-promoting"
        ∷ "No theorem, Clay, or terminal promotion is claimed"
        ∷ []
    }

spanningLemmaKeepsPromotionFalse :
  theoremPromoted canonicalNSTriadBSSpanningLemmaReceipt ≡ false
spanningLemmaKeepsPromotionFalse =
  refl
