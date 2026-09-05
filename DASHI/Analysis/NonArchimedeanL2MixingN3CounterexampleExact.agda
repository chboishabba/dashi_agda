module DASHI.Analysis.NonArchimedeanL2MixingN3CounterexampleExact where

------------------------------------------------------------------------
-- EXACT n=3 COUNTEREXAMPLE TO THE STORED L2 MIXING ASSUMPTION
--
-- For P_3 = D_3 / 2 on Z/8, take
--
--   v = (-1,-1,-1,0,1,1,1,0).
--
-- It is mean-zero.  Directly from the source transition rule
-- P f(x)=1/2(f(3x)+f(3x-1)),
--
--   P_3 v = (-1/2,-1/2,1,-1,1/2,1/2,-1,1).
--
-- Hence
--
--   ||v||_2^2   = 6,
--   ||P_3 v||^2 = 5.
--
-- The source field `spectral_bound_phase3` would imply the squared necessary
-- bound ||P_3 v||^2 <= (1/2)||v||^2 = 3, which is impossible.
--
-- This is a finite rational regression.  No floating point, trigonometry, or
-- spectral-radius-to-operator-norm inference is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_; -_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (toWitness)

------------------------------------------------------------------------
-- Eight residue coordinates.
------------------------------------------------------------------------

data I8 : Set where
  i0 i1 i2 i3 i4 i5 i6 i7 : I8

Vec8 : Set
Vec8 = I8 → ℚ

minusOne : ℚ
minusOne = - 1ℚ

half : ℚ
half = Int.+ 1 / 2

sourceVector : Vec8
sourceVector i0 = minusOne
sourceVector i1 = minusOne
sourceVector i2 = minusOne
sourceVector i3 = 0ℚ
sourceVector i4 = 1ℚ
sourceVector i5 = 1ℚ
sourceVector i6 = 1ℚ
sourceVector i7 = 0ℚ

------------------------------------------------------------------------
-- Literal affine branches modulo 8.
------------------------------------------------------------------------

threeBranch : I8 → I8
threeBranch i0 = i0
threeBranch i1 = i3
threeBranch i2 = i6
threeBranch i3 = i1
threeBranch i4 = i4
threeBranch i5 = i7
threeBranch i6 = i2
threeBranch i7 = i5

threeMinusOneBranch : I8 → I8
threeMinusOneBranch i0 = i7
threeMinusOneBranch i1 = i2
threeMinusOneBranch i2 = i5
threeMinusOneBranch i3 = i0
threeMinusOneBranch i4 = i3
threeMinusOneBranch i5 = i6
threeMinusOneBranch i6 = i1
threeMinusOneBranch i7 = i4

p3 : Vec8 → Vec8
p3 vector x =
  half * (vector (threeBranch x) + vector (threeMinusOneBranch x))

------------------------------------------------------------------------
-- Finite sum and squared L2 norm.
------------------------------------------------------------------------

sum8 : Vec8 → ℚ
sum8 vector =
  vector i0 + vector i1 + vector i2 + vector i3 +
  vector i4 + vector i5 + vector i6 + vector i7

square : ℚ → ℚ
square x = x * x

l2Squared8 : Vec8 → ℚ
l2Squared8 vector =
  square (vector i0) + square (vector i1) +
  square (vector i2) + square (vector i3) +
  square (vector i4) + square (vector i5) +
  square (vector i6) + square (vector i7)

sourceVectorMeanZero : sum8 sourceVector ≡ 0ℚ
sourceVectorMeanZero = solve []

sourceVectorL2SquaredIsSix : l2Squared8 sourceVector ≡ 6
sourceVectorL2SquaredIsSix = solve []

p3SourceVectorL2SquaredIsFive : l2Squared8 (p3 sourceVector) ≡ 5
p3SourceVectorL2SquaredIsFive = solve []

halfSourceSquaredIsThree :
  half * l2Squared8 sourceVector ≡ 3
halfSourceSquaredIsThree = solve []

threeLessFive : (3 : ℚ) < 5
threeLessFive = toWitness {a? = (3 : ℚ) ℚP.<? 5} _

halfSourceSquaredLessThanStepSquared :
  half * l2Squared8 sourceVector < l2Squared8 (p3 sourceVector)
halfSourceSquaredLessThanStepSquared
  rewrite halfSourceSquaredIsThree | p3SourceVectorL2SquaredIsFive =
  threeLessFive

inverseSqrtTwoSquaredNecessaryBoundFails :
  ¬ (l2Squared8 (p3 sourceVector) ≤ half * l2Squared8 sourceVector)
inverseSqrtTwoSquaredNecessaryBoundFails allegedBound =
  ℚP.<⇒≱ halfSourceSquaredLessThanStepSquared allegedBound

record N3MixingCounterexample : Set where
  constructor n3MixingCounterexample
  field
    witnessMeanZero : sum8 sourceVector ≡ 0ℚ
    sourceNormSquared : l2Squared8 sourceVector ≡ 6
    imageNormSquared : l2Squared8 (p3 sourceVector) ≡ 5
    halfSquaredContractionFails :
      ¬ (l2Squared8 (p3 sourceVector) ≤ half * l2Squared8 sourceVector)

canonicalN3MixingCounterexample : N3MixingCounterexample
canonicalN3MixingCounterexample =
  n3MixingCounterexample
    sourceVectorMeanZero
    sourceVectorL2SquaredIsSix
    p3SourceVectorL2SquaredIsFive
    inverseSqrtTwoSquaredNecessaryBoundFails

l2MixingAssumptionRefutedAtN3 : Bool
l2MixingAssumptionRefutedAtN3 = true

l2MixingAssumptionRefutedAtN3IsTrue :
  l2MixingAssumptionRefutedAtN3 ≡ true
l2MixingAssumptionRefutedAtN3IsTrue = refl
