module DASHI.Physics.Closure.NSNormalizedAlignmentBudgetDerivative where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

------------------------------------------------------------------------
-- Division-free quotient-rule surface for the normalized alignment budget.
--
-- E  = packet enstrophy
-- N  = alignment numerator
-- A  = normalized budget, supplied through N = A E
--
-- If N' = A' E + A E', then
--
--     N' E = (A' E) E + N E'.
--
-- This is the exact cross-multiplied quotient rule.  The analytic lane may
-- later recover A' = (N'E - NE')/E² once positivity/invertibility of E has
-- been instantiated in its chosen real-analysis model.
------------------------------------------------------------------------

record BudgetProductArithmetic : Set₁ where
  field
    Scalar : Set
    _+_ _*_ : Scalar → Scalar → Scalar

    multiplyRightDistributesOverAddition :
      (a b c : Scalar) →
      _*_ (_+_ a b) c ≡ _+_ (_*_ a c) (_*_ b c)

    swapMiddleFactors :
      (a b c : Scalar) →
      _*_ (_*_ a b) c ≡ _*_ (_*_ a c) b

open BudgetProductArithmetic public

record NormalizedAlignmentDerivativeInputs
    (R : BudgetProductArithmetic) : Set₁ where
  field
    E N A : Scalar R
    Edot Ndot Adot : Scalar R

    numeratorIsNormalizedTimesEnstrophy :
      N ≡ _*_ R A E

    differentiatedNumeratorIdentity :
      Ndot ≡ _+_ R
        (_*_ R Adot E)
        (_*_ R A Edot)

open NormalizedAlignmentDerivativeInputs public

normalizedAlignmentCrossMultipliedQuotientRule :
  (R : BudgetProductArithmetic) →
  (I : NormalizedAlignmentDerivativeInputs R) →
  _*_ R (Ndot I) (E I) ≡
  _+_ R
    (_*_ R (_*_ R (Adot I) (E I)) (E I))
    (_*_ R (N I) (Edot I))
normalizedAlignmentCrossMultipliedQuotientRule R I =
  trans
    (cong (λ value → _*_ R value (E I))
      (differentiatedNumeratorIdentity I))
    (trans
      (multiplyRightDistributesOverAddition R
        (_*_ R (Adot I) (E I))
        (_*_ R (A I) (Edot I))
        (E I))
      (cong₂ (_+_ R)
        refl
        (trans
          (swapMiddleFactors R (A I) (Edot I) (E I))
          (cong (λ value → _*_ R value (Edot I))
            (sym (numeratorIsNormalizedTimesEnstrophy I))))))
