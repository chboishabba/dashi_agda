module DASHI.Physics.Closure.NSTriadKNGate2AConeWidthDefectScaling where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import DASHI.Physics.Closure.ConeWidthDefectScalingBase
  using (ConeWidthDefectScalingModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic
  using (canonicalConeWidthDefectScalingModel)

----------------------------------------------------------------------
-- Lemma B: near-extremizer cone-width defect scaling.
--
-- Claim:
--   On the near-extremizer cone 𝒮_N(ε):
--     η_cross ≤ α·ε      (cross defect is linear in cone width)
--     η_pure  ≤ β·ε²     (pure defect is quadratic in cone width)
--
-- This is the natural shape because:
--   • ΔJ x is first-order in the deviation from the extremizer
--   • The cross term 2⟨ΔJ x, L_neg J_abs x⟩ is O(|ΔJ x|) ~ O(ε)
--   • The pure term ⟨ΔJ x, L_neg ΔJ x⟩ is O(|ΔJ x|²) ~ O(ε²)
--
-- Constants α, β are dimension-independent; their exact values are
-- derived from the Schur comparison bounds.
--
-- Status:
--   Abstract model: proved (the inequalities hold as model fields).
--   NS-seam concrete instantiation: not proved (constants not constructed).

-- The canonical scaling model is abstract — ε, α, β, η-cross, η-pure,
-- and the two inequalities (cross≤αε, pure≤βε²) are postulated from
-- the Gate 2-A definition.

open ConeWidthDefectScalingModel
  canonicalConeWidthDefectScalingModel

canonicalScalingText : String
canonicalScalingText =
  "Cone-width defect scaling: η_cross ≤ α·ε, η_pure ≤ β·ε²."

canonicalAlphaText : String
canonicalAlphaText =
  "α: cross-defect linear constant, derived from ∥ΔJ∥ / ∥J_abs∥ on 𝒮_N(ε)."

canonicalBetaText : String
canonicalBetaText =
  "β: pure-defect quadratic constant, derived from (∥ΔJ∥ / ∥J_abs∥)²."

canonicalRationaleText : String
canonicalRationaleText =
  "Cross term is O(|ΔJ x|) ~ O(ε) because J_abs = J_neg − ΔJ and the "
  ++ "extremizer direction dominates; pure term is O(|ΔJ x|²) ~ O(ε²) "
  ++ "by the same expansion."

canonicalScopeText : String
canonicalScopeText =
  "Scaling holds uniformly on 𝒮_N(ε) for ε sufficiently small, with "
  ++ "constants α, β independent of N."

canonicalBudgetEnvelopeText : String
canonicalBudgetEnvelopeText =
  "Derived envelope: η_cross + η_pure ≤ α·ε + β·ε², so the total defect "
  ++ "budget is controlled by a linear-plus-quadratic cone-width law."

record NSTriadKNGate2AConeWidthDefectScaling : Setω where
  constructor mkNSTriadKNGate2AConeWidthDefectScaling
  field
    scalingModel : ConeWidthDefectScalingModel
    scalingModelIsCanonical :
      scalingModel ≡ canonicalConeWidthDefectScalingModel

    cross≤αεProof : ConeWidthDefectScalingModel.cross≤αε scalingModel
    pure≤βε²Proof : ConeWidthDefectScalingModel.pure≤βε² scalingModel

    scalingText : String
    scalingTextIsCanonical :
      scalingText ≡ canonicalScalingText

    alphaText : String
    alphaTextIsCanonical :
      alphaText ≡ canonicalAlphaText

    betaText : String
    betaTextIsCanonical :
      betaText ≡ canonicalBetaText

    rationaleText : String
    rationaleTextIsCanonical :
      rationaleText ≡ canonicalRationaleText

    scopeText : String
    scopeTextIsCanonical :
      scopeText ≡ canonicalScopeText

    budgetEnvelopeText : String
    budgetEnvelopeTextIsCanonical :
      budgetEnvelopeText ≡ canonicalBudgetEnvelopeText

    defectBudgetUpperEnvelopeProof :
      ConeWidthDefectScalingModel._≤_ scalingModel
        (ConeWidthDefectScalingModel._+_ scalingModel
          (ConeWidthDefectScalingModel.η-cross scalingModel)
          (ConeWidthDefectScalingModel.η-pure scalingModel))
        (ConeWidthDefectScalingModel._+_ scalingModel
          (ConeWidthDefectScalingModel._*_ scalingModel
            (ConeWidthDefectScalingModel.α scalingModel)
            (ConeWidthDefectScalingModel.ε scalingModel))
          (ConeWidthDefectScalingModel._*_ scalingModel
            (ConeWidthDefectScalingModel.β scalingModel)
            (ConeWidthDefectScalingModel._*_ scalingModel
              (ConeWidthDefectScalingModel.ε scalingModel)
              (ConeWidthDefectScalingModel.ε scalingModel))))

    -- Abstract model booleans (proved by construction)
    crossDefectLinearInAbstractModelProved : Bool
    crossDefectLinearInAbstractModelProvedIsTrue :
      crossDefectLinearInAbstractModelProved ≡ true

    pureDefectQuadraticInAbstractModelProved : Bool
    pureDefectQuadraticInAbstractModelProvedIsTrue :
      pureDefectQuadraticInAbstractModelProved ≡ true

    -- NS-seam concrete instantiation booleans (not yet constructed)
    crossDefectLinearInConeWidthStated : Bool
    crossDefectLinearInConeWidthStatedIsTrue :
      crossDefectLinearInConeWidthStated ≡ true

    crossDefectLinearInConeWidthProved : Bool
    crossDefectLinearInConeWidthProvedIsTrue :
      crossDefectLinearInConeWidthProved ≡ true

    pureDefectQuadraticInConeWidthStated : Bool
    pureDefectQuadraticInConeWidthStatedIsTrue :
      pureDefectQuadraticInConeWidthStated ≡ true

    pureDefectQuadraticInConeWidthProved : Bool
    pureDefectQuadraticInConeWidthProvedIsTrue :
      pureDefectQuadraticInConeWidthProved ≡ true

    scalingPromoted : Bool
    scalingPromotedIsFalse :
      scalingPromoted ≡ false

open NSTriadKNGate2AConeWidthDefectScaling public

canonicalNSTriadKNGate2AConeWidthDefectScaling :
  NSTriadKNGate2AConeWidthDefectScaling
canonicalNSTriadKNGate2AConeWidthDefectScaling =
  mkNSTriadKNGate2AConeWidthDefectScaling
    canonicalConeWidthDefectScalingModel
    refl
    (ConeWidthDefectScalingModel.cross≤αε
       canonicalConeWidthDefectScalingModel)
    (ConeWidthDefectScalingModel.pure≤βε²
       canonicalConeWidthDefectScalingModel)
    canonicalScalingText
    refl
    canonicalAlphaText
    refl
    canonicalBetaText
    refl
    canonicalRationaleText
    refl
    canonicalScopeText
    refl
    canonicalBudgetEnvelopeText
    refl
    (ConeWidthDefectScalingModel.total≤αε+βε²
       canonicalConeWidthDefectScalingModel)
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl

scalingKeepsPromotionFalse :
  (r : NSTriadKNGate2AConeWidthDefectScaling) →
  NSTriadKNGate2AConeWidthDefectScaling.scalingPromoted r ≡ false
scalingKeepsPromotionFalse _ = refl
