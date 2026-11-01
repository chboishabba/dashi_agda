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
--   Cleaner delta = 1 / L2 energy-estimate attack surface:
--     target ratio |<omega,e2>/g12| <= C_*,
--     equivalently |<omega,e2>|^2 <= C_*^2 g12^2.
--   GD1 minimum-gap PDE:
--     F123 ~ -g12^-1 (λ3 - λ1)|<omega,e2>|^2.
--   If the ratio bound is proved, then F123 = O(g12).
--   Preferred boundary-energy route:
--     Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2,
--     with the desired differential estimate d_t Q <= C Q
--     and the Sobolev-on-boundary lift from finite Q under smooth data.
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

  targetRatioBoundRecorded :
    NSCollapseImpossibleCalc11TargetShape

  targetRatioSquaredEquivalentRecorded :
    NSCollapseImpossibleCalc11TargetShape

  gd1MinimumGapPDERouteRecorded :
    NSCollapseImpossibleCalc11TargetShape

  ifRatioBoundedThenF123Og12Recorded :
    NSCollapseImpossibleCalc11TargetShape

  preferredQRouteRecorded :
    NSCollapseImpossibleCalc11TargetShape

  d_tQAtMostCQRecorded :
    NSCollapseImpossibleCalc11TargetShape

  sobolevOnBoundaryLiftRecorded :
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
  ∷ targetRatioBoundRecorded
  ∷ targetRatioSquaredEquivalentRecorded
  ∷ gd1MinimumGapPDERouteRecorded
  ∷ ifRatioBoundedThenF123Og12Recorded
  ∷ preferredQRouteRecorded
  ∷ d_tQAtMostCQRecorded
  ∷ sobolevOnBoundaryLiftRecorded
  ∷ targetInfBoundaryPositiveRecorded
  ∷ calc11NoSpecialAlignmentRecorded
  ∷ clayPromotionFalseRecorded
  ∷ []

collapseImpossibleObligationText : String
collapseImpossibleObligationText =
  "collapseImpossible target receipt: the attack surface is the delta=1 / L2 energy route on ∂Ω_K, namely target ratio |<omega,e2>/g12| <= C_*, equivalently |<omega,e2>|^2 <= C_*^2 g12^2; the GD1 minimum-gap PDE uses F123 ~ -g12^-1 (λ3 - λ1)|<omega,e2>|^2, so any proved ratio bound yields F123 = O(g12), with Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2, d_t Q <= C Q, and a Sobolev-on-boundary lift recorded as the preferred obligation surface only."

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
  ∷ "target ratio |<omega,e2>/g12| <= C_* on ∂Ω_K"
  ∷ "|<omega,e2>|^2 <= C_*^2 g12^2 on ∂Ω_K"
  ∷ "GD1 minimum-gap PDE: F123 ~ -g12^-1 (λ3 - λ1)|<omega,e2>|^2"
  ∷ "If ratio bounded then F123 = O(g12)"
  ∷ "preferred Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2"
  ∷ "desired d_t Q <= C Q"
  ∷ "Sobolev-on-boundary lift from finite Q under smooth data"
  ∷ "calc11 no_special_alignment empirical only"
  ∷ "Clay promotion false"
  ∷ []

targetRatioBoundTextValue : String
targetRatioBoundTextValue =
  "target ratio |<omega,e2>/g12| <= C_* on ∂Ω_K"

targetRatioSquaredEquivalentTextValue : String
targetRatioSquaredEquivalentTextValue =
  "|<omega,e2>|^2 <= C_*^2 g12^2 on ∂Ω_K"

gd1MinimumGapPDERouteTextValue : String
gd1MinimumGapPDERouteTextValue =
  "GD1 minimum-gap PDE: F123 ~ -g12^-1 (λ3 - λ1)|<omega,e2>|^2"

ifRatioBoundedThenF123Og12TextValue : String
ifRatioBoundedThenF123Og12TextValue =
  "If ratio bounded then F123 = O(g12)"

preferredQRouteTextValue : String
preferredQRouteTextValue =
  "preferred Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2"

d_tQAtMostCQTextValue : String
d_tQAtMostCQTextValue =
  "desired d_t Q <= C Q"

sobolevOnBoundaryLiftTextValue : String
sobolevOnBoundaryLiftTextValue =
  "Sobolev-on-boundary lift from finite Q under smooth data"

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

    targetRatioBoundText :
      String

    targetRatioBoundTextIsCanonical :
      targetRatioBoundText ≡ targetRatioBoundTextValue

    targetRatioSquaredEquivalentText :
      String

    targetRatioSquaredEquivalentTextIsCanonical :
      targetRatioSquaredEquivalentText ≡ targetRatioSquaredEquivalentTextValue

    gd1MinimumGapPDERouteText :
      String

    gd1MinimumGapPDERouteTextIsCanonical :
      gd1MinimumGapPDERouteText ≡ gd1MinimumGapPDERouteTextValue

    ifRatioBoundedThenF123Og12Text :
      String

    ifRatioBoundedThenF123Og12TextIsCanonical :
      ifRatioBoundedThenF123Og12Text ≡ ifRatioBoundedThenF123Og12TextValue

    preferredQRouteText :
      String

    preferredQRouteTextIsCanonical :
      preferredQRouteText ≡ preferredQRouteTextValue

    d_tQAtMostCQText :
      String

    d_tQAtMostCQTextIsCanonical :
      d_tQAtMostCQText ≡ d_tQAtMostCQTextValue

    sobolevOnBoundaryLiftText :
      String

    sobolevOnBoundaryLiftTextIsCanonical :
      sobolevOnBoundaryLiftText ≡ sobolevOnBoundaryLiftTextValue

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
    ; targetRatioBoundText =
        targetRatioBoundTextValue
    ; targetRatioBoundTextIsCanonical =
        refl
    ; targetRatioSquaredEquivalentText =
        targetRatioSquaredEquivalentTextValue
    ; targetRatioSquaredEquivalentTextIsCanonical =
        refl
    ; gd1MinimumGapPDERouteText =
        gd1MinimumGapPDERouteTextValue
    ; gd1MinimumGapPDERouteTextIsCanonical =
        refl
    ; ifRatioBoundedThenF123Og12Text =
        ifRatioBoundedThenF123Og12TextValue
    ; ifRatioBoundedThenF123Og12TextIsCanonical =
        refl
    ; preferredQRouteText =
        preferredQRouteTextValue
    ; preferredQRouteTextIsCanonical =
        refl
    ; d_tQAtMostCQText =
        d_tQAtMostCQTextValue
    ; d_tQAtMostCQTextIsCanonical =
        refl
    ; sobolevOnBoundaryLiftText =
        sobolevOnBoundaryLiftTextValue
    ; sobolevOnBoundaryLiftTextIsCanonical =
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
        ∷ "Target ratio route: |<omega,e2>/g12| <= C_* and |<omega,e2>|^2 <= C_*^2 g12^2"
        ∷ "GD1 minimum-gap PDE route: F123 ~ -g12^-1 (λ3 - λ1)|<omega,e2>|^2"
        ∷ "Preferred boundary-energy route: Q(t) = ∫_{∂Ω_K} |<omega,e2>|^2 / g12^2 dH2"
        ∷ "Desired differential route: d_t Q <= C Q with Sobolev-on-boundary lift from finite Q"
        ∷ "If proved, F123 = O(g12) and the singular forcing is not promoted"
        ∷ "Calc 11 no_special_alignment is empirical only and non-promoting"
        ∷ "The diagnostic does not claim collapseImpossible"
        ∷ "Clay promotion remains false"
        ∷ []
    }

targetVarsAndShapesKeepsClayPromotionFalse :
  clayPromotion canonicalNSCollapseImpossibleCalc11TargetReceipt ≡ false
targetVarsAndShapesKeepsClayPromotionFalse = refl

targetRatioBoundTextValueIsCanonical :
  targetRatioBoundText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  targetRatioBoundTextValue
targetRatioBoundTextValueIsCanonical = refl

targetRatioSquaredEquivalentTextValueIsCanonical :
  targetRatioSquaredEquivalentText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  targetRatioSquaredEquivalentTextValue
targetRatioSquaredEquivalentTextValueIsCanonical = refl

gd1MinimumGapPDERouteTextValueIsCanonical :
  gd1MinimumGapPDERouteText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  gd1MinimumGapPDERouteTextValue
gd1MinimumGapPDERouteTextValueIsCanonical = refl

ifRatioBoundedThenF123Og12TextValueIsCanonical :
  ifRatioBoundedThenF123Og12Text canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  ifRatioBoundedThenF123Og12TextValue
ifRatioBoundedThenF123Og12TextValueIsCanonical = refl

preferredQRouteTextValueIsCanonical :
  preferredQRouteText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  preferredQRouteTextValue
preferredQRouteTextValueIsCanonical = refl

d_tQAtMostCQTextValueIsCanonical :
  d_tQAtMostCQText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  d_tQAtMostCQTextValue
d_tQAtMostCQTextValueIsCanonical = refl

sobolevOnBoundaryLiftTextValueIsCanonical :
  sobolevOnBoundaryLiftText canonicalNSCollapseImpossibleCalc11TargetReceipt ≡
  sobolevOnBoundaryLiftTextValue
sobolevOnBoundaryLiftTextValueIsCanonical = refl
