module DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact where

------------------------------------------------------------------------
-- ROUND465 / GENUINE RATIONAL FINITE CS -> PERIODIC SHELL BERNSTEIN
--
-- The generic periodic scalar-CS/Bernstein surfaces carry their inequalities
-- as input fields.  Here the literal rational theorem is derived instead from
-- RationalOrderedFiniteL2 by embedding a scalar list a_i as pairs (a_i , 1).
-- Thus
--
--   (sum a_i)^2 <= length(a) * sum a_i^2.
--
-- Since sum a_i^2 is nonnegative, a natural shell-length bound transports this
-- to the existing infinity-cube count
--
--   27 * 2^(3 n).
--
-- The factor 27 is retained literally.  No monotonicity for negative scalars
-- is requested.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; length)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount as Count
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational

sumCoefficients : List ℚ → ℚ
sumCoefficients [] = 0ℚ
sumCoefficients (x ∷ xs) = x + sumCoefficients xs

sumSquares : List ℚ → ℚ
sumSquares [] = 0ℚ
sumSquares (x ∷ xs) = x * x + sumSquares xs

scaleNat : Nat → ℚ → ℚ
scaleNat zero value = 0ℚ
scaleNat (suc n) value = value + scaleNat n value

pairWithOne : List ℚ → List Rational.Pair
pairWithOne [] = []
pairWithOne (x ∷ xs) = (x , 1ℚ) ∷ pairWithOne xs

pairDotMeaning :
  (xs : List ℚ) →
  Rational.pairDot (pairWithOne xs) ≡ sumCoefficients xs
pairDotMeaning [] = refl
pairDotMeaning (x ∷ xs) =
  trans
    (cong (x * 1ℚ +_) (pairDotMeaning xs))
    (solve (x ∷ sumCoefficients xs ∷ []))

leftNormMeaning :
  (xs : List ℚ) →
  Rational.leftNormSquared (pairWithOne xs) ≡ sumSquares xs
leftNormMeaning [] = refl
leftNormMeaning (x ∷ xs) =
  cong (x * x +_) (leftNormMeaning xs)

rightNormMeaning :
  (xs : List ℚ) →
  Rational.rightNormSquared (pairWithOne xs) ≡ scaleNat (length xs) 1ℚ
rightNormMeaning [] = refl
rightNormMeaning (x ∷ xs) =
  trans
    (cong (1ℚ * 1ℚ +_) (rightNormMeaning xs))
    (solve (scaleNat (length xs) 1ℚ ∷ []))

sumSquaresNonnegative : (xs : List ℚ) → 0ℚ ≤ sumSquares xs
sumSquaresNonnegative [] = ℚP.≤-refl
sumSquaresNonnegative (x ∷ xs) =
  Rational.addNonnegative
    (Rational.squareNonnegative x)
    (sumSquaresNonnegative xs)

scaleNatNonnegative :
  (n : Nat) {value : ℚ} →
  0ℚ ≤ value →
  0ℚ ≤ scaleNat n value
scaleNatNonnegative zero valueNN = ℚP.≤-refl
scaleNatNonnegative (suc n) valueNN =
  Rational.addNonnegative valueNN (scaleNatNonnegative n valueNN)

scaleNatMonotone :
  {m n : Nat} {value : ℚ} →
  0ℚ ≤ value →
  m Cube.≤ᴺ n →
  scaleNat m value ≤ scaleNat n value
scaleNatMonotone valueNN Cube.z≤n = scaleNatNonnegative _ valueNN
scaleNatMonotone valueNN (Cube.s≤s bound) =
  ℚP.+-mono-≤ ℚP.≤-refl (scaleNatMonotone valueNN bound)

scaleNatByOnes :
  (n : Nat) (value : ℚ) →
  value * scaleNat n 1ℚ ≡ scaleNat n value
scaleNatByOnes zero value = solve []
scaleNatByOnes (suc n) value =
  trans
    (solve (value ∷ scaleNat n 1ℚ ∷ []))
    (cong (value +_) (scaleNatByOnes n value))

finiteRationalScalarCauchySchwarzSquared :
  (xs : List ℚ) →
  sumCoefficients xs * sumCoefficients xs
  ≤ scaleNat (length xs) (sumSquares xs)
finiteRationalScalarCauchySchwarzSquared xs =
  let
    source = Rational.finiteCauchySchwarzSquared (pairWithOne xs)
    lhs :
      Rational.square (Rational.pairDot (pairWithOne xs))
      ≡ sumCoefficients xs * sumCoefficients xs
    lhs = cong (λ z → z * z) (pairDotMeaning xs)
    rhs :
      Rational.leftNormSquared (pairWithOne xs)
        * Rational.rightNormSquared (pairWithOne xs)
      ≡ scaleNat (length xs) (sumSquares xs)
    rhs =
      trans
        (cong₂ _*_
          (leftNormMeaning xs)
          (rightNormMeaning xs))
        (scaleNatByOnes (length xs) (sumSquares xs))
  in
  subst
    (λ lower → lower ≤ scaleNat (length xs) (sumSquares xs))
    lhs
    (subst
      (Rational.square (Rational.pairDot (pairWithOne xs)) ≤_)
      rhs source)

rationalScalarCSWithLengthBound :
  (xs : List ℚ) (L : Nat) →
  length xs Cube.≤ᴺ L →
  sumCoefficients xs * sumCoefficients xs
  ≤ scaleNat L (sumSquares xs)
rationalScalarCSWithLengthBound xs L lengthBound =
  ℚP.≤-trans
    (finiteRationalScalarCauchySchwarzSquared xs)
    (scaleNatMonotone (sumSquaresNonnegative xs) lengthBound)

rationalInfinityShellBernsteinSquared :
  (n : Nat) (coefficients : List ℚ) →
  length coefficients Cube.≤ᴺ Count.infinityCubeModeCount n →
  sumCoefficients coefficients * sumCoefficients coefficients
  ≤ scaleNat
      (27 * (Count.pow2 n * (Count.pow2 n * Count.pow2 n)))
      (sumSquares coefficients)
rationalInfinityShellBernsteinSquared n coefficients shellLengthBound =
  rationalScalarCSWithLengthBound coefficients _
    (Cube.≤ᴺ-trans shellLengthBound
      (Count.coarseTwentySevenTimesDyadicCubeBound n))

round465FiniteRationalScalarCSActuallyProved : Bool
round465FiniteRationalScalarCSActuallyProved = true

round465ReusesRationalOrderedFiniteL2 : Bool
round465ReusesRationalOrderedFiniteL2 = true

round465LiteralBernsteinFactorTwentySevenRetained : Bool
round465LiteralBernsteinFactorTwentySevenRetained = true

round465RequiresFalseMonotonicityForNegativeScalars : Bool
round465RequiresFalseMonotonicityForNegativeScalars = false

round465ShellSupportLengthRoutingStillRequired : Bool
round465ShellSupportLengthRoutingStillRequired = true

round465ContainsPostulate : Bool
round465ContainsPostulate = false

round465PackageAClosed : Bool
round465PackageAClosed = false

round465ClayPromotion : Bool
round465ClayPromotion = false

round465RequiresFalseMonotonicityForNegativeScalarsIsFalse :
  round465RequiresFalseMonotonicityForNegativeScalars ≡ false
round465RequiresFalseMonotonicityForNegativeScalarsIsFalse = refl

round465ContainsPostulateIsFalse : round465ContainsPostulate ≡ false
round465ContainsPostulateIsFalse = refl
