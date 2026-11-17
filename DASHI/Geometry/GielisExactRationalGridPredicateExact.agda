{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisExactRationalGridPredicateExact where

------------------------------------------------------------------------
-- Exact selected Gielis 3/6/9 radial MEMBERSHIP on rational grid points.
--
-- For z=x+iy, q=x²+y² and m>0:
--   r_m(theta)=2/sqrt(3+cos(m theta)).
-- At q>0, cos(m theta)=Re(z^m)/q^(m/2), so
--   q < r_m²  iff
--   (3q-4)*q^(m/2) + q*Re(z^m) < 0.
--
-- m even: a rational polynomial strict test.
-- m odd : A*sqrt(q)+B<0 with A,B rational. Eliminate sqrt by
-- explicitly comparing signs and squared rationals; no rounding,
-- no floating trig, no assumed approximate numerical equality.
--
-- This module constructs the concrete original rational decision
-- FUNCTION, with verified selected axis/origin evaluations.
-- The Bishop-real analytic identification is a separate comparison
-- theorem; nothing assumes that two Real carriers are identical.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (yes; no)

isLess : ℚ → ℚ → Bool
isLess a b with ℚP._<?_ a b
... | yes _ = true
... | no _ = false

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true then yesValue else noValue = yesValue
if false then yesValue else noValue = noValue

record RationalComplex : Set where
  constructor complex
  field
    re im : ℚ

open RationalComplex public

complexPow : ℚ → ℚ → Nat → RationalComplex
complexPow x y zero = complex 1ℚ 0ℚ
complexPow x y (suc n) with complexPow x y n
... | complex a b =
  complex (a * x - b * y) (a * y + b * x)

powQ : ℚ → Nat → ℚ
powQ a zero = 1ℚ
powQ a (suc n) = a * powQ a n

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

squareRadius : ℚ → ℚ → ℚ
squareRadius x y = x * x + y * y

-- A<0, B>0: A sqrt(q)+B<0 iff B²<A² q.
-- A>0, B<0: A sqrt(q)+B<0 iff A² q<B².
-- For A<0 and B<=0, strict inequality holds because q>0.
oddRootLessThanZero : ℚ → ℚ → ℚ → Bool
oddRootLessThanZero A B q =
  if isLess A 0ℚ then
    (if isLess 0ℚ B then
       isLess (B * B) ((A * A) * q)
     else true)
  else
    (if isLess 0ℚ A then
       (if isLess B 0ℚ then
          isLess ((A * A) * q) (B * B)
        else false)
     else isLess B 0ℚ)

insideEvenMode : Nat → ℚ → ℚ → Bool
insideEvenMode k x y =
  let q = squareRadius x y in
  if isLess 0ℚ q then
    isLess
      (((3 * q - 4) * powQ q k)
       + (q * re (complexPow x y (twice k))))
      0ℚ
  else true

insideOddMode : Nat → ℚ → ℚ → Bool
insideOddMode k x y =
  let q = squareRadius x y in
  if isLess 0ℚ q then
    oddRootLessThanZero
      ((3 * q - 4) * powQ q k)
      (q * re (complexPow x y (suc (twice k))))
      q
  else true

insideGielis3 : ℚ → ℚ → Bool
insideGielis3 = insideOddMode 1

insideGielis6 : ℚ → ℚ → Bool
insideGielis6 = insideEvenMode 3

insideGielis9 : ℚ → ℚ → Bool
insideGielis9 = insideOddMode 4

originInside3 : insideGielis3 0ℚ 0ℚ ≡ true
originInside3 = refl

originInside6 : insideGielis6 0ℚ 0ℚ ≡ true
originInside6 = refl

originInside9 : insideGielis9 0ℚ 0ℚ ≡ true
originInside9 = refl

-- Along theta=0, the selected radius is exactly 1 for every m.
-- Strict domain membership excludes the boundary point (1,0).
positiveAxisBoundary3 : insideGielis3 1ℚ 0ℚ ≡ false
positiveAxisBoundary3 = refl

positiveAxisBoundary6 : insideGielis6 1ℚ 0ℚ ≡ false
positiveAxisBoundary6 = refl

positiveAxisBoundary9 : insideGielis9 1ℚ 0ℚ ≡ false
positiveAxisBoundary9 = refl
