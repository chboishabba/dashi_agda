module DASHI.Geometry.GielisBishopPolynomialExact where

------------------------------------------------------------------------
-- Native algebra on the ACTUAL vendored Murray/Bishop real carrier.
-- The universal quartic identity below requires NO assumed trigonometry,
-- no new axiomatic Real record, and no postulates.
--
-- Exactly this missing algebraic weld supports G03:
--   4(c^4+s^4)+3(1-(c^2+s^2)^2)
--     = 3+c^4-6c^2*s^2+s^4.
--
-- To specialize c=cos_B(x), s=sin_B(x), the genuine Bishop
-- Pythagorean and 4-angle identities must still be furnished by
-- the concrete sine/cosine owners. Neither identity is manufactured
-- by this polynomial proof.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Trig

square : Bishop.ℝ → Bishop.ℝ
square x = Bishop._*_ x x

fourth : Bishop.ℝ → Bishop.ℝ
fourth x = square (square x)

one two three four six : Bishop.ℝ
one = Bishop._⋆ (+ 1 / 1)
two = Bishop._⋆ (+ 2 / 1)
three = Bishop._⋆ (+ 3 / 1)
four = Bishop._⋆ (+ 4 / 1)
six = Bishop._⋆ (+ 6 / 1)

gielisFourthSum : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
gielisFourthSum c s =
  Bishop._+_ (fourth c) (fourth s)

cosineQuadruplePolynomial : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
cosineQuadruplePolynomial c s =
  Bishop._-_
    (gielisFourthSum c s)
    (Bishop._*_ six
      (Bishop._*_ (square c) (square s)))

pythagoreanSquare : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
pythagoreanSquare c s =
  square (Bishop._+_ (square c) (square s))

gielisCorrectedQuartic : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
gielisCorrectedQuartic c s =
  Bishop._+_
    (Bishop._*_ four (gielisFourthSum c s))
    (Bishop._*_ three
      (Bishop._-_ one (pythagoreanSquare c s)))

gielisCanonicalQuartic : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
gielisCanonicalQuartic c s =
  Bishop._+_ three (cosineQuadruplePolynomial c s)

-- Genuine algebraic equality on the concrete Bishop real setoid.
-- Uses the same BishopP.ℝ-Solver as the canonical golden ratio and
-- positive-reciprocal owners.
bishopGielisUniversalQuarticNormalForm :
  ∀ c s →
  Bishop._≃_
    (gielisCorrectedQuartic c s)
    (gielisCanonicalQuartic c s)
bishopGielisUniversalQuarticNormalForm c s =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ a b →
      ( (Κ (+ 4 / 1)
          ⊗ ((a ⊗ a ⊗ a ⊗ a)
              ⊕ (b ⊗ b ⊗ b ⊗ b)))
        ⊕
        (Κ (+ 3 / 1)
          ⊗
          (Κ (+ 1 / 1)
            ⊖
            (((a ⊗ a) ⊕ (b ⊗ b))
             ⊗ ((a ⊗ a) ⊕ (b ⊗ b)))))
      ⊜
      (Κ (+ 3 / 1)
       ⊕
       (((a ⊗ a ⊗ a ⊗ a)
          ⊕ (b ⊗ b ⊗ b ⊗ b))
         ⊖
         (Κ (+ 6 / 1) ⊗ ((a ⊗ a) ⊗ (b ⊗ b))))))
    BishopP.≃-refl c s

-- An explicit same-Bishop-real trigonometric consumer.
-- This does NOT equate a conditional argument with a constructed witness.
-- It exposes exactly the concrete Pythagorean and quadruple-angle inputs
-- that the existing Bishop trig series must pay before G03 closes.
record BishopGielisConcreteTrigInputs
    (dataSet : Trig.BishopElementaryPowerSeriesData)
    (angle : Bishop.ℝ) : Set where
  field
    pythagorean :
      Bishop._≃_
        (Bishop._+_
          (square (Trig.bishopCos dataSet angle))
          (square (Trig.bishopSin dataSet angle)))
        one
    cosineQuadruple :
      Bishop._≃_
        (Trig.bishopCos dataSet
          (Bishop._*_ four angle))
        (cosineQuadruplePolynomial
          (Trig.bishopCos dataSet angle)
          (Trig.bishopSin dataSet angle))

-- Unlike a terminal one-point real carrier, these inputs are about the
-- actual same BishopReal.ℝ and the same existing sine/cosine functions.
