module DASHI.Analysis.PolarJacobianDeterminantAlgebraExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans; cong)

------------------------------------------------------------------------
-- EXACT POLAR JACOBIAN DETERMINANT ALGEBRA
--
-- For the formal derivative matrix
--
--   [[ c, -r s ],
--    [ s,  r c ]]
--
-- the determinant is r(c^2+s^2), hence r once c^2+s^2=1.
--
-- This is pure 2x2/ring algebra.  It does NOT prove that c=cos(theta),
-- s=sin(theta), that these are the actual derivatives of the polar chart, or
-- that a measure-theoretic change-of-variables theorem applies.
------------------------------------------------------------------------

record Matrix2 : Set where
  constructor matrix2
  field
    m00 m01 m10 m11 : ℚ

open Matrix2 public

determinant2 : Matrix2 → ℚ
determinant2 M = m00 M * m11 M - m01 M * m10 M

polarDerivativeMatrix : ℚ → ℚ → ℚ → Matrix2
polarDerivativeMatrix r c s =
  matrix2 c (- (r * s)) s (r * c)

polarDeterminantIsRadiusTimesPythagorean :
  (r c s : ℚ) →
  determinant2 (polarDerivativeMatrix r c s)
  ≡ r * (c * c + s * s)
polarDeterminantIsRadiusTimesPythagorean r c s =
  solve (r ∷ c ∷ s ∷ [])

polarDeterminantIsRadius :
  (r c s : ℚ) →
  c * c + s * s ≡ 1ℚ →
  determinant2 (polarDerivativeMatrix r c s) ≡ r
polarDeterminantIsRadius r c s pythagorean =
  trans
    (polarDeterminantIsRadiusTimesPythagorean r c s)
    (trans
      (cong (r *_) pythagorean)
      (solve (r ∷ [])))

record PolarJacobianAlgebraReceipt : Set where
  field
    radius cosine sine : ℚ
    pythagorean : cosine * cosine + sine * sine ≡ 1ℚ
    determinantLaw :
      determinant2 (polarDerivativeMatrix radius cosine sine) ≡ radius

open PolarJacobianAlgebraReceipt public

buildPolarJacobianAlgebraReceipt :
  (r c s : ℚ) →
  c * c + s * s ≡ 1ℚ →
  PolarJacobianAlgebraReceipt
buildPolarJacobianAlgebraReceipt r c s pyth = record
  { radius = r
  ; cosine = c
  ; sine = s
  ; pythagorean = pyth
  ; determinantLaw = polarDeterminantIsRadius r c s pyth
  }
