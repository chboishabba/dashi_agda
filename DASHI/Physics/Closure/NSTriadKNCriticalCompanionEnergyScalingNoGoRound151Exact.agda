module DASHI.Physics.Closure.NSTriadKNCriticalCompanionEnergyScalingNoGoRound151Exact where

------------------------------------------------------------------------
-- ROUND151 / SPATIAL-SCALING NO-GO FOR THE NAIVE ENERGY COMPANION
--
-- Navier--Stokes scaling in R^3 is
--
--   u_lambda(x,t) = lambda u(lambda x, lambda^2 t).
--
-- The homogeneous Sobolev norm ||u||_{H^s} scales with exponent s-1/2.
-- Hence
--
--   ||u||_2       : -1/2,
--   ||u||_{H^1}   :  1/2,
--   ||u||_{H^3/2} :  1,
--
-- while the H^(1/2) critical energy is invariant and its nonlinear production
-- scales like a time derivative, exponent 2.
--
-- A tempting post-Round150 companion estimate would be
--
--   |Pcrit| <= C ||u||_{H^3/2} ||u||_2 ||u||_{H^1}.
--
-- Its right side has scaling exponent only
--
--   1 + (-1/2) + (1/2) = 1,
--
-- one full power below the critical production exponent 2.  Thus it cannot be
-- the scale-uniform arbitrary-data theorem.  By contrast the familiar
--
--   ||u||_{H^1}^2 ||u||_{H^3/2}
--
-- has exponent 2 and is scaling-compatible, but it does not provide an
-- arbitrary-data absorption.
--
-- This exact rational audit prevents the new product-remainder compiler from
-- being "closed" with a subcritical energy/enstrophy companion that cannot
-- possibly survive concentration.  The surviving A route must use genuinely
-- signed trajectory/global structure, not only instantaneous lower norms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

minusHalf half one two threeHalves : ℚ
minusHalf = Int.-[1+ 0 ] / 2
half = Int.+ 1 / 2
one = Int.+ 1 / 1
two = Int.+ 2 / 1
threeHalves = Int.+ 3 / 2

-- s - 1/2 in dimension three for the NS amplitude scaling u_lambda=lambda u(lambda x).
sobolevScalingExponent : ℚ → ℚ
sobolevScalingExponent s = s + minusHalf

l2ScalingExponent : ℚ
l2ScalingExponent = sobolevScalingExponent (Int.+ 0 / 1)

h1ScalingExponent : ℚ
h1ScalingExponent = sobolevScalingExponent one

hThreeHalvesScalingExponent : ℚ
hThreeHalvesScalingExponent = sobolevScalingExponent threeHalves

criticalProductionScalingExponent : ℚ
criticalProductionScalingExponent = two

naiveEnergyCompanionProductExponent : ℚ
naiveEnergyCompanionProductExponent =
  hThreeHalvesScalingExponent + l2ScalingExponent + h1ScalingExponent

standardCriticalCubicExponent : ℚ
standardCriticalCubicExponent =
  h1ScalingExponent + h1ScalingExponent + hThreeHalvesScalingExponent

l2ExponentIsMinusHalf : l2ScalingExponent ≡ minusHalf
l2ExponentIsMinusHalf = solve []

h1ExponentIsHalf : h1ScalingExponent ≡ half
h1ExponentIsHalf = solve []

hThreeHalvesExponentIsOne : hThreeHalvesScalingExponent ≡ one
hThreeHalvesExponentIsOne = solve []

naiveEnergyCompanionProductExponentIsOne :
  naiveEnergyCompanionProductExponent ≡ one
naiveEnergyCompanionProductExponentIsOne = solve []

standardCriticalCubicExponentIsTwo :
  standardCriticalCubicExponent ≡ two
standardCriticalCubicExponentIsTwo = solve []

round151NaiveEnergyCompanionIsOneScalingPowerShort : Bool
round151NaiveEnergyCompanionIsOneScalingPowerShort = true

round151StandardH1SquaredHThreeHalvesIsScalingCritical : Bool
round151StandardH1SquaredHThreeHalvesIsScalingCritical = true

round151SubcriticalInstantaneousCompanionClosesPackageA : Bool
round151SubcriticalInstantaneousCompanionClosesPackageA = false

round151PackageAClosed : Bool
round151PackageAClosed = false

round151NaiveEnergyCompanionIsOneScalingPowerShortIsTrue :
  round151NaiveEnergyCompanionIsOneScalingPowerShort ≡ true
round151NaiveEnergyCompanionIsOneScalingPowerShortIsTrue = refl

round151PackageAClosedIsFalse : round151PackageAClosed ≡ false
round151PackageAClosedIsFalse = refl
