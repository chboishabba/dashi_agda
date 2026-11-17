{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRationalS3StereographicNodeExact where

------------------------------------------------------------------------
-- ORIGINAL SU2 SOURCE: rational, exact S3 nodes WITHOUT sqrt, pi,
-- algebraic root towers, or a supplied norm-one witness.
--
-- Given three rational parameters x,y,z and an inverse for the
-- explicitly positive denominator d=1+x²+y²+z², the polynomial
-- Pythagorean identity constructs the ORIGINAL
-- BalabanSU2RationalWilsonLargeFieldGapExact.RationalUnitQuaternion.
-- The norm witness is DERIVED here by the rational ring solver.
--
-- Source inverse law: Data.Rational.Properties.*-inverseʳ, available
-- once the explicit positive denominator has been proved nonzero.
-- This source isolates exactly that elementary order obligation.
--
-- It does not assert that a finite rational net already has exact
-- Haar moments or that a Bishop limit has been kernel accepted.
-- Attribution: classical stereographic sphere construction; existing
-- DASHI rational quaternion owners; Bishop/Bridges; Wilson/Balaban.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Original

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

square : ℚ → ℚ
square x = x * x

radialSquare : ℚ → ℚ → ℚ → ℚ
radialSquare x y z = square x + square y + square z

denominator : ℚ → ℚ → ℚ → ℚ
denominator x y z = 1ℚ + radialSquare x y z

stereoA : ℚ → ℚ → ℚ → ℚ
stereoA x y z = 1ℚ - radialSquare x y z

stereoB stereoC stereoD : ℚ → ℚ
stereoB x = twoℚ * x
stereoC y = twoℚ * y
stereoD z = twoℚ * z

numeratorNorm :
  ∀ x y z →
  square (stereoA x y z) +
  square (stereoB x) +
  square (stereoC y) +
  square (stereoD z)
  ≡ square (denominator x y z)
numeratorNorm = ℚRing.solve-∀

scaledNormRegroup :
  ∀ a b c d inv →
  square (a * inv) + square (b * inv) +
  square (c * inv) + square (d * inv)
  ≡ (square a + square b + square c + square d) * square inv
scaledNormRegroup = ℚRing.solve-∀

denominatorNormRegroup :
  ∀ d inv →
  square d * square inv ≡ square (d * inv)
denominatorNormRegroup = ℚRing.solve-∀

oneSquared : square 1ℚ ≡ 1ℚ
oneSquared = ℚRing.solve-∀

-- This is the original quaternion's REQUIRED record field,
-- proven from the polynomial relation, not supplied by a caller.
stereoNormFromReciprocal :
  ∀ x y z inv →
  denominator x y z * inv ≡ 1ℚ →
  square (stereoA x y z * inv) +
  square (stereoB x * inv) +
  square (stereoC y * inv) +
  square (stereoD z * inv)
  ≡ 1ℚ
stereoNormFromReciprocal x y z inv inverseLaw =
  trans
    (scaledNormRegroup
      (stereoA x y z) (stereoB x) (stereoC y) (stereoD z) inv)
    (trans
      (cong (λ norm → norm * square inv)
        (numeratorNorm x y z))
      (trans
        (denominatorNormRegroup (denominator x y z) inv)
        (trans
          (cong square inverseLaw)
          oneSquared)))

originalSU2RationalStereographicNode :
  ∀ x y z inv →
  denominator x y z * inv ≡ 1ℚ →
  Original.RationalUnitQuaternion
originalSU2RationalStereographicNode x y z inv inverseLaw =
  Original.rationalUnitQuaternion
    (stereoA x y z * inv)
    (stereoB x * inv)
    (stereoC y * inv)
    (stereoD z * inv)
    (stereoNormFromReciprocal x y z inv inverseLaw)

-- The remaining scalar step is NOT an assumed sphere node:
-- instantiate inv via the pre-existing stdlib rational reciprocal
-- and prove 1+x²+y²+z² positive from squares.
