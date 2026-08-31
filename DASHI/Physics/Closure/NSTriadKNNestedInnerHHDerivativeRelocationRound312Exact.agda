module DASHI.Physics.Closure.NSTriadKNNestedInnerHHDerivativeRelocationRound312Exact where

------------------------------------------------------------------------
-- ROUND312 / INNER HETEROCHIRAL HH NULL RELOCATES THE DERIVATIVE TO OUTPUT p
--
-- In the nested carrier a+b=p, p+q=k, R310 pairs the inner ordered Galerkin
-- terms into the R120 helical multiplier-difference commutator.
--
-- On the heterochiral HH->low child, the signed eigenvalue difference has one
-- high-frequency factor ~ 2^m, while the opposite-helicity cross product has
-- the R232 null factor ~ 2^(j-m), where |a|~|b|~2^m and |p|~2^j.
-- Their product is therefore ~ 2^j: the derivative scale is relocated from the
-- high inner inputs to the low inner output p.
--
-- This file records the exact dyadic exponent arithmetic only.  The physical
-- same-object weld from the R120 vector and R232 symbol estimate remains an
-- analytic producer and is not replaced by the exponent calculation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two : ℚ
one = 1
two = one + one

innerHighDerivativeExponent : ℚ → ℚ
innerHighDerivativeExponent high = high

innerHeterochiralNullExponent : ℚ → ℚ → ℚ
innerHeterochiralNullExponent output high = output - high

innerRelocatedAmplitudeExponent : ℚ → ℚ → ℚ
innerRelocatedAmplitudeExponent output high =
  innerHighDerivativeExponent high
  + innerHeterochiralNullExponent output high

innerRelocatedAmplitudeIsOutput :
  (output high : ℚ) →
  innerRelocatedAmplitudeExponent output high ≡ output
innerRelocatedAmplitudeIsOutput output high = solve (output ∷ high ∷ [])

innerHighDerivativeSquaredExponent : ℚ → ℚ
innerHighDerivativeSquaredExponent high = two * high

innerHeterochiralNullSquaredExponent : ℚ → ℚ → ℚ
innerHeterochiralNullSquaredExponent output high = two * (output - high)

innerRelocatedSquaredExponent : ℚ → ℚ → ℚ
innerRelocatedSquaredExponent output high =
  innerHighDerivativeSquaredExponent high
  + innerHeterochiralNullSquaredExponent output high

innerRelocatedSquaredIsTwoOutput :
  (output high : ℚ) →
  innerRelocatedSquaredExponent output high ≡ two * output
innerRelocatedSquaredIsTwoOutput output high = solve (output ∷ high ∷ [])

round312InnerHeterochiralHHDerivativeRelocatedToOutput : Bool
round312InnerHeterochiralHHDerivativeRelocatedToOutput = true

round312InnerHighDerivativeSurvivesAfterNullGain : Bool
round312InnerHighDerivativeSurvivesAfterNullGain = false

round312PhysicalR120R232SameObjectWeldClosed : Bool
round312PhysicalR120R232SameObjectWeldClosed = false

round312NestedOuterCriticalConePaid : Bool
round312NestedOuterCriticalConePaid = false

round312PackageAClosed : Bool
round312PackageAClosed = false

round312ClayPromotion : Bool
round312ClayPromotion = false
