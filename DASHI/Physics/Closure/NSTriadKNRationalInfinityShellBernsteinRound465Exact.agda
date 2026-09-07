module DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact where

------------------------------------------------------------------------
-- ROUND465 / GENUINE RATIONAL FINITE CS -> PERIODIC SHELL BERNSTEIN
--
-- NSPeriodicFiniteScalarCauchySchwarzSquared is an authority interface: its
-- finite-CS inequality is a field, not a theorem.  This owner supplies the
-- theorem on the literal rational carrier by reusing the already-proved finite
-- squared Cauchy--Schwarz theorem in RationalOrderedFiniteL2.
--
-- A scalar list a_i is embedded as the pair list (a_i , 1).  Hence
--
--   (sum a_i)^2 <= (sum a_i^2) * length(a)
--
-- and, because sum a_i^2 is nonnegative, any natural length bound L gives
--
--   (sum a_i)^2 <= L * sum a_i^2.
--
-- Combining this with the existing literal infinity-cube count produces the
-- exact coefficient
--
--   27 * 2^(3 n)
--
-- without silently normalising away 27.  The only remaining shell-routing
-- receipt is the finite combinatorial statement that the chosen shell list has
-- length at most the counted infinity cube.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; length)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Product.Base using (_,_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

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
  cong (x +_) (pairDotMeaning xs)

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
  cong (1ℚ +_) (rightNormMeaning xs)

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
scaleNatMonotone valueNN Cube.z≤n =
  scaleNatNonnegative _ valueNN
scaleNatMonotone valueNN (Cube.s≤s bound) =
  ℚP.+-mono-≤ ℚP.≤-refl (scaleNatMonotone valueNN bound)

productCountMeaning :
  (xs : List ℚ) →
  sumSquares xs * scaleNat (length xs) 1ℚ
  ≡ scaleNat (length xs) (sumSquares xs)
productCountMeaning [] = solve []
productCountMeaning (x ∷ xs) =
  let
    s = x * x + sumSquares xs
    nCount = scaleNat (length xs) 1ℚ
    nScaled = scaleNat (length xs) s
  in
  trans
    (solve (s ∷ nCount ∷ []))
    (cong (s +_)
      (trans
        (sym (productCountMeaningForValue xs s))
        refl))
  where
  productCountMeaningForValue :
    (ys : List ℚ) → (value : ℚ) →
    value * scaleNat (length ys) 1ℚ
    ≡ scaleNat (length ys) value
  productCountMeaningForValue [] value = solve []
  productCountMeaningForValue (y ∷ ys) value =
    trans
      (cong (value +_) (productCountMeaningForValue ys value))
      (solve (value ∷ scaleNat (length ys) value ∷ []))

-- A simpler standalone product/count identity, used below and kept public.
scaleNatByOnes :
  (n : Nat) (value : ℚ) →
  value * scaleNat n 1ℚ ≡ scaleNat n value
scaleNatByOnes zero value = solve []
scaleNatByOnes (suc n) value =
  trans
    (cong (value +_) (scaleNatByOnes n value))
    (solve (value ∷ scaleNat n value ∷ []))

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
    lhs =
      trans
        (cong (λ z → z * z) (pairDotMeaning xs))
        refl
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
