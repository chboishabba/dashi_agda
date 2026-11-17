module DASHI.Physics.YangMills.YMClayRationalS3StereographicConcreteExact where

------------------------------------------------------------------------
-- COMPLETE RATIONAL S3 NODE, not an assumed quaternion norm witness:
-- x,y,z are ANY ORIGINAL reduced rationals. The denominator
-- d=1+x²+y²+z² is PROVED positive, then inverted using the original
-- rational positive-mass reciprocal owner. The exact Pythagorean
-- proof lives in YMClayRationalS3StereographicNodeExact.
--
-- This file is deliberately NOT --safe, because it imports the
-- existing non-safe BalabanBoolean4BlockPoincareExact and
-- BalabanClayGate4RationalPositiveMassReciprocalExact owners.
-- No trust promotion until the full transitive Agda check.
--
-- This constructs EXACT rational S3 points. Moment quadrature and
-- Bishop continuous completion are separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _≤_; _<_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact as PositiveSquares
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.YMClayRationalS3StereographicNodeExact as Stereo
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Original

radialSquareNonnegative :
  ∀ x y z →
  0ℚ ≤ Stereo.radialSquare x y z
radialSquareNonnegative x y z =
  ℚP.+-mono-≤
    (ℚP.+-mono-≤
      (PositiveSquares.squareNonnegative x)
      (PositiveSquares.squareNonnegative y))
    (PositiveSquares.squareNonnegative z)

denominatorPositive :
  ∀ x y z → Positive (Stereo.denominator x y z)
denominatorPositive x y z =
  subst
    (λ left → left < Stereo.denominator x y z)
    (ℚRing.solve [])
    (ℚP.+-mono-<-≤
      ℚP.0<1
      (radialSquareNonnegative x y z))

stereoInverse : ℚ → ℚ → ℚ → ℚ
stereoInverse x y z =
  Reciprocal.safeRationalReciprocal (Stereo.denominator x y z)

stereoInverseLaw :
  ∀ x y z →
  Stereo.denominator x y z * stereoInverse x y z ≡ 1ℚ
stereoInverseLaw x y z =
  let
    d = Stereo.denominator x y z
    inverse = stereoInverse x y z
  in
  subst
    (λ result → result ≡ 1ℚ)
    (ℚP.*-comm d inverse)
    (Reciprocal.safeRationalReciprocalTimesPositive
      d (denominatorPositive x y z))

-- Literal original-source finite SU2 carrier. No user-supplied norm.
rationalS3Node :
  ℚ → ℚ → ℚ → Original.RationalUnitQuaternion
rationalS3Node x y z =
  Stereo.originalSU2RationalStereographicNode
    x y z
    (stereoInverse x y z)
    (stereoInverseLaw x y z)
