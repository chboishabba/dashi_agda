module DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP-COMPLEX NORM-SQUARE UPPER ENVELOPE.
--
-- Existing BishopComplexNormSquarePowerEnvelopeExact requires an exact
-- radius identity normSq(q) ~= r*r, unavailable from an arbitrary
-- Bishop CLOSED DISK where only normSq(q) <= r*r is given.
--
-- This module proves the inequality version without any square root:
--
--   normSq(q) <= r*r
--       => normSq(q^n) <= (r^n)*(r^n)
--       => |Re(q^n)|,|Im(q^n)| <= r^n.
--
-- The constructive Bishop real ordered-ring inequalities and the
-- already-proved nonnegative square reflection are the only inputs.
-- This is the appropriate finite source majorant for the original
-- Bishop log(1+u) series on a DISK, not merely a sphere.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflection

normSquareNonnegative :
  ∀ q → BishopReal.NonNegative (Norm.normSqC q)
normSquareNonnegative (Complex.complex a b) =
  BishopP.nonNegx,y⇒nonNegx+y
    (SquareNN.bishopSquareNonnegative a)
    (SquareNN.bishopSquareNonnegative b)

record BishopComplexNormSquareUpperRadius
    (q : Complex.BishopComplex)
    (radius : BishopReal.ℝ) : Set₁ where
  field
    radiusNonnegative : BishopReal.NonNegative radius
    normSqBelowRadiusSquare :
      BishopReal._≤_ (Norm.normSqC q) (Norm.square radius)

open BishopComplexNormSquareUpperRadius public

radiusSquareSuccessor :
  ∀ r n →
  BishopReal._≃_
    (BishopReal._*_
      (Norm.square r)
      (Norm.square (BishopReal.pow r n)))
    (Norm.square (BishopReal.pow r (suc n)))
radiusSquareSuccessor r n =
  let open BishopP.ℝ-Solver in
  solve 2
    (λ radius oldPower →
      (radius ⊗ radius) ⊗ (oldPower ⊗ oldPower)
      ⊜ (oldPower ⊗ radius) ⊗ (oldPower ⊗ radius))
    BishopP.≃-refl r (BishopReal.pow r n)

normSquarePowerUpper :
  ∀ {q r} →
  (upper : BishopComplexNormSquareUpperRadius q r) →
  ∀ n →
  BishopReal._≤_
    (Norm.normSqC (Algebra.powC q n))
    (Norm.square (BishopReal.pow r n))
normSquarePowerUpper upper zero =
  let open BishopP.ℝ-Solver in
  BishopP.≤-respˡ-≃
    (Norm.normSqOne)
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (solve 0
          (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1) ⊜ Κ (+ 1 / 1))
          BishopP.≃-refl))
      BishopP.≤-refl)
normSquarePowerUpper {q} {r} upper (suc n) =
  BishopP.≤-respˡ-≃
    (Norm.normSqMultiply q (Algebra.powC q n))
    (BishopP.≤-respʳ-≃
      (radiusSquareSuccessor r n)
      (BishopP.*-mono-≤
        (normSquareNonnegative q)
        (normSquareNonnegative (Algebra.powC q n))
        (normSqBelowRadiusSquare upper)
        (normSquarePowerUpper upper n)))

componentAbsolutePowerUpper :
  ∀ {q r} →
  (upper : BishopComplexNormSquareUpperRadius q r) →
  (n : Nat) →
  (component : BishopReal.ℝ) →
  BishopReal._≤_
    (Norm.square component)
    (Norm.normSqC (Algebra.powC q n)) →
  BishopReal._≤_
    (BishopReal.∣_∣ component)
    (BishopReal.pow r n)
componentAbsolutePowerUpper {q} {r} upper n component below =
  Reflection.squareReflectsOnNonnegative
    (BishopP.nonNeg∣x∣ component)
    (BishopSequence.nonNegx⇒nonNegxⁿ n
      (radiusNonnegative upper))
    (BishopP.≤-respˡ-≃
      (Norm.absoluteSquare component)
      (BishopP.≤-trans
        below
        (normSquarePowerUpper upper n)))

realPowerUpper :
  ∀ {q r} →
  BishopComplexNormSquareUpperRadius q r →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣_∣
      (Complex.re (Algebra.powC q n)))
    (BishopReal.pow r n)
realPowerUpper {q} upper n =
  componentAbsolutePowerUpper upper n
    (Complex.re (Algebra.powC q n))
    (Norm.componentSquareBelowNormSqReal (Algebra.powC q n))

imagPowerUpper :
  ∀ {q r} →
  BishopComplexNormSquareUpperRadius q r →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣_∣
      (Complex.im (Algebra.powC q n)))
    (BishopReal.pow r n)
imagPowerUpper {q} upper n =
  componentAbsolutePowerUpper upper n
    (Complex.im (Algebra.powC q n))
    (Norm.componentSquareBelowNormSqImag (Algebra.powC q n))
