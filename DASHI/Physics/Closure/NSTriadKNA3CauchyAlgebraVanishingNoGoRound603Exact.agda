{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3CauchyAlgebraVanishingNoGoRound603Exact where

------------------------------------------------------------------------
-- ROUND603 / NO-GO: R291 + CAUCHY INVERSION DO NOT FORCE R601 VANISHING
--
-- R600/R601 reduce the dynamic representation question to the scalar pair law
--
--   C(a,b)
--     = 2 R K(a,b) N(a,b)
--       + (n(r(a)+r(b)) - 2 R) G(a,b),
--
-- under
--
--   T(a,b) = -(r(a)+r(b)) G(a,b) + N(a,b)
--   K(a,b) (r(a)+r(b)) = 1.
--
-- It is tempting to hope that those two identities alone force C=0.  They do
-- not.  The one-point rational model below satisfies both exact laws while
-- C(*) = 1.
--
-- This does NOT say the literal Navier--Stokes carrier cannot enjoy an
-- additional physical cancellation.  It proves only that such a cancellation
-- is not finite algebra already contained in R291 + Cauchy inversion.  Any
-- closure of the R598/R601 mismatch must use additional physical structure or
-- a genuine estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; trans)

import DASHI.Physics.Closure.NSTriadKNA3CenteredCauchyPairNormalFormRound600Exact as R600

data One : Set where
  star : One

half : ℚ
half = Int.+ 1 / 2

n603 : ℚ
n603 = 1ℚ

rateTotal603 : ℚ
rateTotal603 = half

rate603 : One → ℚ
rate603 star = half

kernel603 : One → One → ℚ
kernel603 star star = 1ℚ

gram603 : One → One → ℚ
gram603 star star = 0ℚ

nonlinear603 : One → One → ℚ
nonlinear603 star star = 1ℚ

tangent603 : One → One → ℚ
tangent603 star star = 1ℚ

tangentLaw603 :
  (a b : One) →
  tangent603 a b
  ≡ (0ℚ - (rate603 a + rate603 b)) * gram603 a b
      + nonlinear603 a b
tangentLaw603 star star = solve []

cauchyInverseLaw603 :
  (a b : One) →
  kernel603 a b * (rate603 a + rate603 b) ≡ 1ℚ
cauchyInverseLaw603 star star = solve []

dynamicPair603 : One → One → ℚ
dynamicPair603 =
  R600.centeredDynamicPair
    n603 rateTotal603 rate603
    kernel603 gram603 tangent603

remainderPair603 : One → One → ℚ
remainderPair603 =
  R600.centeredDynamicRemainderPair
    n603 rateTotal603 rate603
    kernel603 gram603 nonlinear603

r291CauchyReduction603 :
  dynamicPair603 star star ≡ remainderPair603 star star
r291CauchyReduction603 =
  R600.centeredDynamicPointwiseR291
    n603 rateTotal603
    rate603 kernel603 gram603 tangent603 nonlinear603
    tangentLaw603 cauchyInverseLaw603
    star star

remainderAtStarIsOne603 :
  remainderPair603 star star ≡ 1ℚ
remainderAtStarIsOne603 = solve []

dynamicAtStarIsOne603 :
  dynamicPair603 star star ≡ 1ℚ
dynamicAtStarIsOne603 =
  trans r291CauchyReduction603 remainderAtStarIsOne603

oneNotZero603 : 1ℚ ≢ 0ℚ
oneNotZero603 ()

remainderDoesNotVanish603 :
  remainderPair603 star star ≢ 0ℚ
remainderDoesNotVanish603 equality =
  oneNotZero603
    (trans (sym remainderAtStarIsOne603) equality)

dynamicDoesNotVanish603 :
  dynamicPair603 star star ≢ 0ℚ
dynamicDoesNotVanish603 equality =
  oneNotZero603
    (trans (sym dynamicAtStarIsOne603) equality)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round603R291AndCauchyLawsSatisfiedByWitness : Bool
round603R291AndCauchyLawsSatisfiedByWitness = true

round603CenteredDynamicRemainderCanBeNonzero : Bool
round603CenteredDynamicRemainderCanBeNonzero = true

round603PureFiniteAlgebraForcesMismatchVanishing : Bool
round603PureFiniteAlgebraForcesMismatchVanishing = false

round603AdditionalPhysicalStructureOrEstimateRequired : Bool
round603AdditionalPhysicalStructureOrEstimateRequired = true

round603ClaimsLiteralNSMismatchIsNonzero : Bool
round603ClaimsLiteralNSMismatchIsNonzero = false

round603R291AndCauchyLawsSatisfiedByWitnessIsTrue :
  round603R291AndCauchyLawsSatisfiedByWitness ≡ true
round603R291AndCauchyLawsSatisfiedByWitnessIsTrue = refl

round603CenteredDynamicRemainderCanBeNonzeroIsTrue :
  round603CenteredDynamicRemainderCanBeNonzero ≡ true
round603CenteredDynamicRemainderCanBeNonzeroIsTrue = refl

round603PureFiniteAlgebraForcesMismatchVanishingIsFalse :
  round603PureFiniteAlgebraForcesMismatchVanishing ≡ false
round603PureFiniteAlgebraForcesMismatchVanishingIsFalse = refl

round603AdditionalPhysicalStructureOrEstimateRequiredIsTrue :
  round603AdditionalPhysicalStructureOrEstimateRequired ≡ true
round603AdditionalPhysicalStructureOrEstimateRequiredIsTrue = refl

round603ClaimsLiteralNSMismatchIsNonzeroIsFalse :
  round603ClaimsLiteralNSMismatchIsNonzero ≡ false
round603ClaimsLiteralNSMismatchIsNonzeroIsFalse = refl
