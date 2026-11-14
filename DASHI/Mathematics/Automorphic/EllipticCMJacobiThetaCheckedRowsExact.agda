module DASHI.Mathematics.Automorphic.EllipticCMJacobiThetaCheckedRowsExact where

------------------------------------------------------------------------
-- ORIGINAL CURVE E : y² = x³ - x, CONDUCTOR 32.
-- GAUSSIAN / JACOBI THETA MODEL, ACTUAL FROBENIUS ROWS.
--
-- The published Jacobi-factor identity is
--   eta(4z)^2 eta(8z)^2
--     = (sum_{n>=0} (-1)^n (2n+1) q^((2n+1)^2))
--       * (1 + 2 sum_{m>=1} (-1)^m q^(4m²)).
--
-- For p <= 19 the coefficient can be computed EXACTLY from
-- n in {0,1} and m in {0,1,2}: all later exponents exceed 19.
-- This module computes those literal theta coefficients and joins
-- them to the original seven checked E(F_p) Frobenius traces.
--
-- THIS IS NOT A PROOF OF THE INFINITE JACOBI PRODUCT IDENTITY,
-- a modular form, Mellin integral or the elliptic L(E,1).
-- The finite comparison is a genuine exact arithmetic witness,
-- not a fabricated "modularity receipt".
--
-- Sources: Jacobi identities, Martin–Ono eta CM factorization,
-- E:y²=x³-x original Frobenius row owner in DASHI.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
open import Relation.Nullary using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact as Rows
import DASHI.Mathematics.Automorphic.EllipticSelectedHeckePrimePowerExact as Hecke

two : Nat
two = suc (suc zero)

three : Nat
three = suc two

four : Nat
four = two * two

-- Odd Gaussian real coordinate (2n+1), even imaginary coordinate 2m.
oddCoordinate : Nat → Nat
oddCoordinate n = two * n + suc zero

gaussianNorm : Nat → Nat → Nat
gaussianNorm n m =
  oddCoordinate n * oddCoordinate n + four * m * m

alternatingSign : Nat → ℚ
alternatingSign zero = 1ℚ
alternatingSign (suc n) = - alternatingSign n

jacobiOddWeight : Nat → ℚ
jacobiOddWeight n =
  alternatingSign n * Rows.natToRational (oddCoordinate n)

jacobiEvenWeight : Nat → ℚ
jacobiEvenWeight zero = 1ℚ
jacobiEvenWeight (suc m) =
  Rows.natToRational two * alternatingSign (suc m)

gaussianThetaContribution : Nat → Nat → Nat → ℚ
gaussianThetaContribution target n m
  with NatP._≟_ (gaussianNorm n m) target
... | yes _ = jacobiOddWeight n * jacobiEvenWeight m
... | no _ = 0ℚ

gaussianThetaSumM : Nat → Nat → Nat → ℚ
gaussianThetaSumM target n zero = 0ℚ
gaussianThetaSumM target n (suc m) =
  gaussianThetaSumM target n m +
  gaussianThetaContribution target n m

gaussianThetaSumN : Nat → Nat → ℚ
gaussianThetaSumN target zero = 0ℚ
gaussianThetaSumN target (suc n) =
  gaussianThetaSumN target n +
  gaussianThetaSumM target n three

-- Contains all representations q^p for p <= 19, because
-- n >= 2 entails (2n+1)² >= 25 and
-- m >= 3 entails (2m)² >= 36.
cmThetaCoefficientThrough19 : Nat → ℚ
cmThetaCoefficientThrough19 target =
  gaussianThetaSumN target two

-- Coefficients explicitly on the original seven checked p rows,
-- not merely agreement between two copies of one candidate field.
thetaP3MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 3
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p3Row)
thetaP3MatchesOriginalFrobenius = refl

thetaP5MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 5
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p5Row)
thetaP5MatchesOriginalFrobenius = refl

thetaP7MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 7
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p7Row)
thetaP7MatchesOriginalFrobenius = refl

thetaP11MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 11
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p11Row)
thetaP11MatchesOriginalFrobenius = refl

thetaP13MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 13
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p13Row)
thetaP13MatchesOriginalFrobenius = refl

thetaP17MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 17
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p17Row)
thetaP17MatchesOriginalFrobenius = refl

thetaP19MatchesOriginalFrobenius :
  cmThetaCoefficientThrough19 19
  ≡ Rows.signedToRational (Rows.frobeniusTrace Rows.p19Row)
thetaP19MatchesOriginalFrobenius = refl

-- The normalized level-32 candidate starts q + O(q⁵).
thetaNormalizedFirstCoefficient :
  cmThetaCoefficientThrough19 1 ≡ 1ℚ
thetaNormalizedFirstCoefficient = refl

thetaFirstCompositeCoefficient :
  cmThetaCoefficientThrough19 9
  ≡ Hecke.primePowerHeckeCoefficient
       (Rows.signedToRational (Rows.frobeniusTrace Rows.p3Row))
       (Rows.natToRational 3) two
thetaFirstCompositeCoefficient = refl

-- q^9 has coefficient -3, agreeing with 1 - 3T²
-- from the actual p=3 good Euler denominator (a₃=0).
thetaQ9IsMinusThree :
  cmThetaCoefficientThrough19 9
  ≡ - Rows.natToRational 3
thetaQ9IsMinusThree = refl
