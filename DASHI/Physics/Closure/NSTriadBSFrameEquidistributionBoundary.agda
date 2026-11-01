module DASHI.Physics.Closure.NSTriadBSFrameEquidistributionBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only Biot-Savart frame-equidistribution boundary.
--
-- This is the sharpened finite-dimensional Wall 1 theorem target:
--
--   || K_N - 1/2 I ||_op -> 0
--
-- equivalently
--
--   L_neg = 1/2 L_abs + o(L_abs)
--
-- on the gauge quotient / positive subspace.  The lower spectral edge yields
-- the Wall 1 floor, and the upper spectral edge yields frame safety.  No
-- theorem, full-NS, or Clay promotion is claimed here.

frameEquidistributionStatement : String
frameEquidistributionStatement =
  "Candidate theorem target: || K_N - 1/2 I ||_op -> 0 on the gauge quotient / positive subspace."

negativeFrameEquidistributionStatement : String
negativeFrameEquidistributionStatement =
  "Equivalent candidate theorem target: L_neg = 1/2 L_abs + o(L_abs)."

data NSTriadBSFrameEquidistributionBoundaryStatus : Set where
  candidateOnlyFrameEquidistributionRecorded :
    NSTriadBSFrameEquidistributionBoundaryStatus

data NSTriadBSFrameEquidistributionBoundaryBlocker : Set where
  operatorConcentrationStillOpen :
    NSTriadBSFrameEquidistributionBoundaryBlocker
  dependencyControlStillOpen :
    NSTriadBSFrameEquidistributionBoundaryBlocker
  noPromotionFromEquidistributionBoundary :
    NSTriadBSFrameEquidistributionBoundaryBlocker

canonicalNSTriadBSFrameEquidistributionBoundaryBlockers :
  List NSTriadBSFrameEquidistributionBoundaryBlocker
canonicalNSTriadBSFrameEquidistributionBoundaryBlockers =
  operatorConcentrationStillOpen
  ∷ dependencyControlStillOpen
  ∷ noPromotionFromEquidistributionBoundary
  ∷ []

data NSTriadBSFrameEquidistributionBoundaryPromotion : Set where

nSTriadBSFrameEquidistributionBoundaryPromotionImpossibleHere :
  NSTriadBSFrameEquidistributionBoundaryPromotion →
  ⊥
nSTriadBSFrameEquidistributionBoundaryPromotionImpossibleHere ()

record NSTriadBSFrameEquidistributionBoundaryReceipt : Setω where
  field
    status :
      NSTriadBSFrameEquidistributionBoundaryStatus

    statusIsCandidateOnly :
      status ≡ candidateOnlyFrameEquidistributionRecorded

    theoremTarget :
      String

    theoremTargetIsCanonical :
      theoremTarget ≡ frameEquidistributionStatement

    equivalentNegativeFrameStatement :
      String

    equivalentNegativeFrameStatementIsCanonical :
      equivalentNegativeFrameStatement ≡ negativeFrameEquidistributionStatement

    lowerEdgeControlsFloor :
      Bool

    lowerEdgeControlsFloorIsTrue :
      lowerEdgeControlsFloor ≡ true

    upperEdgeControlsFrameSafety :
      Bool

    upperEdgeControlsFrameSafetyIsTrue :
      upperEdgeControlsFrameSafety ≡ true

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

    fullNSPromoted :
      Bool

    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List NSTriadBSFrameEquidistributionBoundaryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSTriadBSFrameEquidistributionBoundaryBlockers

    promotionFlags :
      List NSTriadBSFrameEquidistributionBoundaryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSTriadBSFrameEquidistributionBoundaryReceipt public

canonicalNSTriadBSFrameEquidistributionBoundaryReceipt :
  NSTriadBSFrameEquidistributionBoundaryReceipt
canonicalNSTriadBSFrameEquidistributionBoundaryReceipt =
  record
    { status =
        candidateOnlyFrameEquidistributionRecorded
    ; statusIsCandidateOnly =
        refl
    ; theoremTarget =
        frameEquidistributionStatement
    ; theoremTargetIsCanonical =
        refl
    ; equivalentNegativeFrameStatement =
        negativeFrameEquidistributionStatement
    ; equivalentNegativeFrameStatementIsCanonical =
        refl
    ; lowerEdgeControlsFloor =
        true
    ; lowerEdgeControlsFloorIsTrue =
        refl
    ; upperEdgeControlsFrameSafety =
        true
    ; upperEdgeControlsFrameSafetyIsTrue =
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
    ; fullNSPromoted =
        false
    ; fullNSPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; blockers =
        canonicalNSTriadBSFrameEquidistributionBoundaryBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The exact Wall 1 theorem target is frame equidistribution around 1/2 I"
        ∷ "Lower spectral edge controls the floor and upper spectral edge controls frame safety"
        ∷ "The route remains candidate-only and non-promoting"
        ∷ []
    }

frameEquidistributionKeepsPromotionFalse :
  theoremPromoted canonicalNSTriadBSFrameEquidistributionBoundaryReceipt ≡ false
frameEquidistributionKeepsPromotionFalse =
  refl
