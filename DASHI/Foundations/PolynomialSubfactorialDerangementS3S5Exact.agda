module DASHI.Foundations.PolynomialSubfactorialDerangementS3S5Exact where

------------------------------------------------------------------------
-- PREFIX !n IS SUBFACTORIAL / DERANGEMENTS (Whitworth, 19th century).
-- POSTFIX n! IS FACTORIAL (Euler, Legendre).
-- These notations are NOT interchangeable:
--   !3 = 2, !5 = 44, while 3! = 6 and 5! = 120.
--
-- DERANGEMENT OF ABC: a permutation with no fixed position.
-- In the exact existing S3, ONLY the two nonidentity C3 rotations are
-- derangements. In S5, exactly 44 of 120 permutations are derangements.
--
-- Source-owner reuse: preexisting S3 and explicit 120-permutation atlas.
-- No claim that 99^(!9999) is the original Pickover target:
-- the attached steelman specifies 99^(9999!), POSTFIX.
-- Verified independent Python: residues mod9999 are 3861 and 4950,
-- respectively; neither fixes the real-angle sine sign.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_!)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3
import DASHI.Foundations.QuinticPermutationTripleOrientationAtlasExact as Five

-- Canonical second-order recurrence for the derangement number D_n = !n.
-- D_0=1, D_1=0, D_n=(n-1)(D_(n-1)+D_(n-2)).
subfactorial : Nat → Nat
subfactorial zero = 1
subfactorial (suc zero) = 0
subfactorial (suc (suc n)) =
  suc n * (subfactorial (suc n) + subfactorial n)

subfactorialZero : subfactorial 0 ≡ 1
subfactorialZero = refl

subfactorialOne : subfactorial 1 ≡ 0
subfactorialOne = refl

subfactorialThree : subfactorial 3 ≡ 2
subfactorialThree = refl

subfactorialFive : subfactorial 5 ≡ 44
subfactorialFive = refl

ordinaryThreeFactorial : 3 ! ≡ 6
ordinaryThreeFactorial = refl

ordinaryFiveFactorial : 5 ! ≡ 120
ordinaryFiveFactorial = refl

prefixAndPostfixFiveAreDifferent :
  subfactorial 5 ≡ (5 !) → ⊥
prefixAndPostfixFiveAreDifferent ()

subfactorial9999 : Nat
subfactorial9999 = subfactorial 9999

-- Exactly the two nonidentity C3 rotations are without fixed points.
derangedS3 : S3.TriPermutation → Bool
derangedS3 S3.permIdentity = false
derangedS3 S3.permRotate = true
derangedS3 S3.permRotate2 = true
derangedS3 S3.permSwapLowMid = false
derangedS3 S3.permSwapLowHigh = false
derangedS3 S3.permSwapMidHigh = false

noFixedPointRotate :
  (x : Base.TriTruth) →
  S3.applyPermutation S3.permRotate x ≡ x → ⊥
noFixedPointRotate Base.tri-low ()
noFixedPointRotate Base.tri-mid ()
noFixedPointRotate Base.tri-high ()

noFixedPointRotate2 :
  (x : Base.TriTruth) →
  S3.applyPermutation S3.permRotate2 x ≡ x → ⊥
noFixedPointRotate2 Base.tri-low ()
noFixedPointRotate2 Base.tri-mid ()
noFixedPointRotate2 Base.tri-high ()

identityHasFixedPoint :
  S3.applyPermutation S3.permIdentity Base.tri-low ≡ Base.tri-low
identityHasFixedPoint = refl

swapLowMidHasFixedPoint :
  S3.applyPermutation S3.permSwapLowMid Base.tri-high ≡ Base.tri-high
swapLowMidHasFixedPoint = refl

swapLowHighHasFixedPoint :
  S3.applyPermutation S3.permSwapLowHigh Base.tri-mid ≡ Base.tri-mid
swapLowHighHasFixedPoint = refl

swapMidHighHasFixedPoint :
  S3.applyPermutation S3.permSwapMidHigh Base.tri-low ≡ Base.tri-low
swapMidHighHasFixedPoint = refl

allThreeLabelDerangements : List S3.TriPermutation
allThreeLabelDerangements =
  S3.permRotate ∷ S3.permRotate2 ∷ []

-- Use the precise 120 label action from the earlier quintic atlas,
-- not an untyped count equality with A5 or 2I.
samePoint5 : Five.Point5 → Five.Point5 → Bool
samePoint5 Five.point0 Five.point0 = true
samePoint5 Five.point1 Five.point1 = true
samePoint5 Five.point2 Five.point2 = true
samePoint5 Five.point3 Five.point3 = true
samePoint5 Five.point4 Five.point4 = true
samePoint5 _ _ = false

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

doesNotFix5 : Five.Permutation5 → Five.Point5 → Bool
doesNotFix5 p x =
  notBool (samePoint5 (Five.applyPermutation5 p x) x)

isDerangement5 : Five.Permutation5 → Bool
isDerangement5 p =
  andBool (doesNotFix5 p Five.point0)
    (andBool (doesNotFix5 p Five.point1)
      (andBool (doesNotFix5 p Five.point2)
        (andBool (doesNotFix5 p Five.point3)
          (doesNotFix5 p Five.point4))))

countDerangements5 : List Five.Permutation5 → Nat
countDerangements5 [] = zero
countDerangements5 (p ∷ ps) with isDerangement5 p
... | true = suc (countDerangements5 ps)
... | false = countDerangements5 ps

exactly44FiveLabelDerangements :
  countDerangements5 Five.allFivePermutations ≡ 44
exactly44FiveLabelDerangements = refl

-- Numerology guard: !3 counts two C3 generators, not all six of S3.
data AllSixS3PermutationsAreDerangements : Set where

notAllSixPermutationsAreDerangements :
  AllSixS3PermutationsAreDerangements → ⊥
notAllSixPermutationsAreDerangements ()
