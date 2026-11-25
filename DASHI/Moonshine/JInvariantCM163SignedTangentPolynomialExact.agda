module DASHI.Moonshine.JInvariantCM163SignedTangentPolynomialExact where

-- Source-written, uncompiled. Integer polynomial certificates for the
-- original degree-41 transverse Taylor calculation. Their interpretation
-- at the actual complex tangent requires a ring-homomorphism proof.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver

tangent : ℤ → ℤ
tangent x = (+ 41) * (x * x) + (+ 81) * x + (+ 41)

-- The signed discriminant coordinate is 82 alpha + 81.
signedDiscriminant : (x : ℤ) →
  ((+ 82) * x + (+ 81)) * ((+ 82) * x + (+ 81)) + (+ 163)
    ≡ (+ 164) * tangent x
signedDiscriminant x =
  solve 1
    (λ a →
      ((con (+ 82) :* a :+ con (+ 81)) :*
       (con (+ 82) :* a :+ con (+ 81))) :+ con (+ 163)
      := con (+ 164) :*
         (con (+ 41) :* (a :* a) :+ con (+ 81) :* a :+ con (+ 41)))
    refl x

-- Two polynomial identities replace the quadratic-field inverse.
cubicFactor : (x : ℤ) →
  (+ 41) * ((+ 1) + x * (x * x)) +
    (+ 122) * (x * (x + (+ 1)))
    ≡ (x + (+ 1)) * tangent x
cubicFactor x =
  solve 1
    (λ a →
      con (+ 41) :* (con (+ 1) :+ a :* (a :* a))
      :+ con (+ 122) :* (a :* (a :+ con (+ 1)))
      := (a :+ con (+ 1)) :*
         (con (+ 41) :* (a :* a) :+ con (+ 81) :* a :+ con (+ 41)))
    refl x

derivativeFactor : (x : ℤ) →
  ((+ 82) * x + (+ 81)) * (x + (- (+ 1))) +
    (+ 163) * (x + (+ 1))
    ≡ (+ 2) * tangent x
derivativeFactor x =
  solve 1
    (λ a →
      (con (+ 82) :* a :+ con (+ 81)) :* (a :+ con (- (+ 1)))
      :+ con (+ 163) :* (a :+ con (+ 1))
      := con (+ 2) :*
         (con (+ 41) :* (a :* a) :+ con (+ 81) :* a :+ con (+ 41)))
    refl x

tangentAtZero : tangent (+ 0) ≡ + 41
tangentAtZero = refl

tangentAtOne : tangent (+ 1) ≡ + 163
tangentAtOne = refl

tangentAtMinusOne : tangent (- (+ 1)) ≡ + 1
tangentAtMinusOne = refl

-- P3=2*(c30+c21), S3=c30. Keep signed coefficients.
diagonalSliceNumerator : (c30 c21 : ℤ) →
  (+ 41) * ((+ 2) * (c30 + c21)) + (- (+ 326)) * c30
    ≡ (+ 2) * ((+ 41) * c21 + (- (+ 122)) * c30)
diagonalSliceNumerator c30 c21 =
  solve 2
    (λ a b →
      con (+ 41) :* (con (+ 2) :* (a :+ b)) :+ con (- (+ 326)) :* a
      := con (+ 2) :* (con (+ 41) :* b :+ con (- (+ 122)) :* a))
    refl c30 c21
