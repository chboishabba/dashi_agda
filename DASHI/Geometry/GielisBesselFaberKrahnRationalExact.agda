{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisBesselFaberKrahnRationalExact where

------------------------------------------------------------------------
-- SOURCE-NATIVE rational certificate used in the Faber-Krahn
-- continuum Gielis lowest-Dirichlet-eigenvalue theorem:
--
-- Area(Ω_m)=sqrt(2)*pi for EVERY positive integer m.
-- 1st Bessel J0 root j_{0,1} > 12/5.
-- sqrt(2) < 99/70.
-- Hence lambda1(Ω_m) > (12/5)^2 * (70/99) = 224/55.
--
-- This file pays the exact finite Bessel-J0 alternating S5
-- polynomial certificate, sqrt(2) rational upper and bound
-- arithmetic on the original rational carrier. The classical
-- Bessel derivative/alternating extension and Faber-Krahn
-- functional analytic theorem are separate analytic donors.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (subst; sym)

a : ℚ
a = (+ 36) / 25

j0S5 : ℚ
j0S5 =
  1ℚ
  - ((+ 36) / 25)
  + ((+ 324) / 625)
  - ((+ 1296) / 15625)
  + ((+ 2916) / 390625)
  - ((+ 104976) / 244140625)

expectedJ0S5 : ℚ
expectedJ0S5 = (+ 608149) / 244140625

j0S5Exact :
  j0S5 ≡ expectedJ0S5
j0S5Exact = Ring.solve []

expectedJ0S5StrictPositive :
  0ℚ < expectedJ0S5
expectedJ0S5StrictPositive =
  toWitness (ℚP._<?_ 0ℚ expectedJ0S5)

j0S5StrictPositive : 0ℚ < j0S5
j0S5StrictPositive =
  subst (0ℚ <_) (sym j0S5Exact)
    expectedJ0S5StrictPositive

j1FirstRatioAtEndpoint : ℚ
j1FirstRatioAtEndpoint = (+ 18) / 25

j1AlternatingUniformLower : ℚ
j1AlternatingUniformLower = (+ 7) / 25

j1FirstRatioBelowOne :
  j1FirstRatioAtEndpoint < 1ℚ
j1FirstRatioBelowOne =
  toWitness (ℚP._<?_ j1FirstRatioAtEndpoint 1ℚ)

j1AlternatingUniformLowerPositive :
  0ℚ < j1AlternatingUniformLower
j1AlternatingUniformLowerPositive =
  toWitness (ℚP._<?_ 0ℚ j1AlternatingUniformLower)

j1UniformLowerExact :
  1ℚ - j1FirstRatioAtEndpoint
  ≡ j1AlternatingUniformLower
j1UniformLowerExact = Ring.solve []

sqrtTwoRationalUpper : ℚ
sqrtTwoRationalUpper = (+ 99) / 70

two : ℚ
two = (+ 2) / 1

sqrtTwoUpperSquareAboveTwo :
  two < sqrtTwoRationalUpper * sqrtTwoRationalUpper
sqrtTwoUpperSquareAboveTwo =
  toWitness
    (ℚP._<?_ two (sqrtTwoRationalUpper * sqrtTwoRationalUpper))

firstBesselZeroRationalLower : ℚ
firstBesselZeroRationalLower = (+ 12) / 5

eigenvalueRationalLower : ℚ
eigenvalueRationalLower = (+ 224) / 55

eigenvalueLowerArithmeticExact :
  ((firstBesselZeroRationalLower * firstBesselZeroRationalLower)
   * ((+ 70) / 99))
  ≡ eigenvalueRationalLower
eigenvalueLowerArithmeticExact = Ring.solve []

eigenvalueRationalLowerAboveFour :
  (+ 4) / 1 < eigenvalueRationalLower
eigenvalueRationalLowerAboveFour =
  toWitness
    (ℚP._<?_ ((+ 4) / 1) eigenvalueRationalLower)

-- The LARGER theorem lambda1(Ω_m)>224/55 additionally requires
-- the original exact area proof and classical Faber-Krahn,
-- Bessel-disk eigenvalue, J0'=-J1 and alternating-series lemmas.
-- They are not manufactured from the rational S5 receipt.
