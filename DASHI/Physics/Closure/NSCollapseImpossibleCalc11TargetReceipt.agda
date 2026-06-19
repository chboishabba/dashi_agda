module DASHI.Physics.Closure.NSCollapseImpossibleCalc11TargetReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only receipt for the collapseImpossible analytic target after
-- Calc 11.
--
-- This records the exact obligation surface only:
--   u, T*, ∂Ω_K, component C, g12 = λ₂ - λ₁, e2, omega = curl u,
--   F123 = -(g12)^-1 * ((λ3 - λ1)|<ω,e2>|² + ...),
--   target inf_{x∈∂C} g12(x,t) > 0 for t < T*.
--
-- Calc 11 is recorded as a no_special_alignment diagnostic in TG Re=1600.
-- It is a candidate-only signal and does not prove the theorem.
-- Clay promotion remains false.

data NSCollapseImpossibleCalc11TargetStatus : Set where
  candidateOnlyClayHardAnalyticTheoremRecorded :
    NSCollapseImpossibleCalc11TargetStatus

data NSCollapseImpossibleCalc11TargetShape : Set where
  uRecorded :
    NSCollapseImpossibleCalc11TargetShape

  tStarRecorded :
    NSCollapseImpossibleCalc11TargetShape

  partialOmegaKRecorded :
    NSCollapseImpossibleCalc11TargetShape

  componentCRecorded :
    NSCollapseImpossibleCalc11TargetShape

  g12EqualsLambda2MinusLambda1Recorded :
    NSCollapseImpossibleCalc11TargetShape

  e2Recorded :
    NSCollapseImpossibleCalc11TargetShape

  omegaEqualsCurlURecorded :
    NSCollapseImpossibleCalc11TargetShape

  F123Recorded :
    NSCollapseImpossibleCalc11TargetShape

  targetInfBoundaryPositiveRecorded :
    NSCollapseImpossibleCalc11TargetShape

  calc11NoSpecialAlignmentRecorded :
    NSCollapseImpossibleCalc11TargetShape

  clayPromotionFalseRecorded :
    NSCollapseImpossibleCalc11TargetShape

canonicalNSCollapseImpossibleCalc11TargetShape :
  List NSCollapseImpossibleCalc11TargetShape
canonicalNSCollapseImpossibleCalc11TargetShape =
  uRecorded
  ∷ tStarRecorded
  ∷ partialOmegaKRecorded
  ∷ componentCRecorded
  ∷ g12EqualsLambda2MinusLambda1Recorded
  ∷ e2Recorded
  ∷ omegaEqualsCurlURecorded
  ∷ F123Recorded
  ∷ targetInfBoundaryPositiveRecorded
  ∷ calc11NoSpecialAlignmentRecorded
  ∷ clayPromotionFalseRecorded
  ∷ []

collapseImpossibleObligationText : String
collapseImpossibleObligationText =
  "collapseImpossible obligation: for the analytic target, the dangerous F123/g12 commutator requires <omega,e2> staying away from zero near collapsing g12, with the boundary target inf_{x∈∂C} g12(x,t) > 0 for t < T*."

calc11ImplicationText : String
calc11ImplicationText =
  "Calc 11 implication: in TG Re=1600, the diagnostic records no_special_alignment for the omega/e2 projection, but this remains a candidate-only signal and does not prove collapseImpossible."

clayHardAnalyticTheoremClassText : String
clayHardAnalyticTheoremClassText =
  "Clay-hard analytic theorem"

targetVarsAndShapesText : List String
targetVarsAndShapesText =
  "u"
  ∷ "T*"
  ∷ "∂Ω_K"
  ∷ "component C"
  ∷ "g12 = λ₂ - λ₁"
  ∷ "e2"
  ∷ "omega = curl u"
  ∷ "F123 = -(g12)^-1 * ((λ3 - λ1)|<ω,e2>|² + ...)"
  ∷ "target inf_{x∈∂C} g12(x,t) > 0 for t < T*"
  ∷ "calc11 no_special_alignment"
  ∷ "Clay promotion false"
  ∷ []

record NSCollapseImpossibleCalc11TargetReceipt : Set where
  field
    status :
      NSCollapseImpossibleCalc11TargetStatus

    statusIsCanonical :
      status ≡ candidateOnlyClayHardAnalyticTheoremRecorded

    analyticClass :
      String

    analyticClassIsCanonical :
      analyticClass ≡ clayHardAnalyticTheoremClassText

    targetVarsAndShapes :
      List String

    targetVarsAndShapesAreCanonical :
      targetVarsAndShapes ≡ targetVarsAndShapesText

    collapseImpossibleObligation :
      String

    collapseImpossibleObligationIsCanonical :
      collapseImpossibleObligation ≡ collapseImpossibleObligationText

    calc11Implication :
      String

    calc11ImplicationIsCanonical :
      calc11Implication ≡ calc11ImplicationText

    calc11NoSpecialAlignment :
      Bool

    calc11NoSpecialAlignmentIsTrue :
      calc11NoSpecialAlignment ≡ true

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    clayProofClaim :
      Bool

    clayProofClaimIsFalse :
      clayProofClaim ≡ false

    receiptBoundary :
      List String

open NSCollapseImpossibleCalc11TargetReceipt public

canonicalNSCollapseImpossibleCalc11TargetReceipt :
  NSCollapseImpossibleCalc11TargetReceipt
canonicalNSCollapseImpossibleCalc11TargetReceipt =
  record
    { status =
        candidateOnlyClayHardAnalyticTheoremRecorded
    ; statusIsCanonical =
        refl
    ; analyticClass =
        clayHardAnalyticTheoremClassText
    ; analyticClassIsCanonical =
        refl
    ; targetVarsAndShapes =
        targetVarsAndShapesText
    ; targetVarsAndShapesAreCanonical =
        refl
    ; collapseImpossibleObligation =
        collapseImpossibleObligationText
    ; collapseImpossibleObligationIsCanonical =
        refl
    ; calc11Implication =
        calc11ImplicationText
    ; calc11ImplicationIsCanonical =
        refl
    ; calc11NoSpecialAlignment =
        true
    ; calc11NoSpecialAlignmentIsTrue =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; clayProofClaim =
        false
    ; clayProofClaimIsFalse =
        refl
    ; receiptBoundary =
        "Candidate-only receipt for the collapseImpossible analytic target after Calc 11"
        ∷ "Exact obligation surface: u, T*, ∂Ω_K, component C, g12 = λ₂ - λ₁, e2, omega = curl u, and F123"
        ∷ "Calc 11 is a no_special_alignment diagnostic in TG Re=1600"
        ∷ "The diagnostic does not prove collapseImpossible"
        ∷ "Clay promotion remains false"
        ∷ []
    }

targetVarsAndShapesKeepsClayPromotionFalse :
  clayPromotion canonicalNSCollapseImpossibleCalc11TargetReceipt ≡ false
targetVarsAndShapesKeepsClayPromotionFalse = refl
