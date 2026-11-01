{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.StressEnergyWeldMathematicalCoreValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.StressEnergyWeldMathematicalCoreExact as C
import DASHI.Physics.Foundations.CMP119GRAnchoredStressMathematicalCoreExact as M

promotionTokenNotMathPremise :
  C.stressWeldPromotionTokenIsMathematicalEqualityPremise ≡ false
promotionTokenNotMathPremise = refl

cmp119MathCoreNeedsNoPromotionToken :
  M.promotionTokenRequiredToProveMathematicalStressEquality ≡ false
cmp119MathCoreNeedsNoPromotionToken = refl
