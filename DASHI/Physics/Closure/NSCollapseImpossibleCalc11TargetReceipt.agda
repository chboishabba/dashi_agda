module DASHI.Physics.Closure.NSCollapseImpossibleCalc11TargetReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only receipt for the collapseImpossible analytic target after
-- Calc 11, recorded as empirical-only and non-promoting.
--
-- This records the exact obligation surface only:
--   u, T*, ∂Ω_K, component C, C_*, delta, E0, ||u0||H1,
--   g12 = λ₂ - λ₁, e2, omega = curl u, F123.
--   Sharp estimate on ∂Ω_K for smooth finite-energy NS:
--     |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0.
--   Hence
--     F123 ~ -g12^-1(λ3 - λ1)|<omega,e2>|^2 = O(g12^delta),
--   which removes the singular forcing.
--
-- Calc 11 is recorded as a no_special_alignment diagnostic in TG Re=1600.
-- It is empirical only, non-promoting, and does not prove collapseImpossible.
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
  "collapseImpossible target receipt: on ∂Ω_K, the estimate |<omega,e2>|^2 <= C_* g12^(1+delta), delta > 0, implies F123 = O(g12^delta) whenever the bound is proved, so the singular forcing is removed; the receipt records g12 = λ₂ - λ₁, omega = curl u, e2, F123, E0, and ||u0||H1 without claiming collapseImpossible."

calc11ImplicationText : String
calc11ImplicationText =
  "Calc 11 implication: in TG Re=1600, the diagnostic records no_special_alignment for the omega/e2 projection, but this is empirical only, non-promoting, and does not prove collapseImpossible."

clayHardAnalyticTheoremClassText : String
clayHardAnalyticTheoremClassText =
  "Clay-hard analytic theorem"

targetVarsAndShapesText : List String
targetVarsAndShapesText =
  "u"
  ∷ "T*"
  ∷ "∂Ω_K"
  ∷ "component C"
  ∷ "C_*"
  ∷ "delta"
  ∷ "E0"
  ∷ "||u0||H1"
  ∷ "g12 = λ₂ - λ₁"
  ∷ "e2"
  ∷ "omega = curl u"
  ∷ "F123 = -(g12)^-1 * ((λ3 - λ1)|<ω,e2>|² + ...)"
  ∷ "|<omega,e2>|^2 <= C_* g12^(1+delta) on ∂Ω_K"
  ∷ "F123 = O(g12^delta)"
  ∷ "calc11 no_special_alignment empirical only"
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
        ∷ "Exact variables: C_*, delta, E0, ||u0||H1, g12 = λ₂ - λ₁, omega = curl u, e2, and F123"
        ∷ "Sharp boundary estimate: |<omega,e2>|^2 <= C_* g12^(1+delta) on ∂Ω_K"
        ∷ "If proved, F123 = O(g12^delta) and the singular forcing is removed"
        ∷ "Calc 11 no_special_alignment is empirical only and non-promoting"
        ∷ "The diagnostic does not claim collapseImpossible"
        ∷ "Clay promotion remains false"
        ∷ []
    }

targetVarsAndShapesKeepsClayPromotionFalse :
  clayPromotion canonicalNSCollapseImpossibleCalc11TargetReceipt ≡ false
targetVarsAndShapesKeepsClayPromotionFalse = refl
