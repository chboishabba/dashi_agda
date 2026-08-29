module DASHI.Physics.Closure.NSTriadKNMixedHelicityScaleNormalizedDefectRound237Exact where

------------------------------------------------------------------------
-- ROUND237 / SCALE-NORMALIZED MIXED-HELICITY DEFECT
--
-- For the Navier--Stokes scaling
--
--   u_lambda(t,x) = lambda u(lambda^2 t, lambda x),
--
-- the L2 energy scales with exponent -1.  The spacetime mixed-helicity defect
--
--   Integral || u+ x u- ||_2^2 dt
--
-- also scales with exponent -1: amplitude^4 contributes +4, space contributes
-- -3 and time contributes -2.  Hence their ratio is scale invariant.
--
-- For two independently scaled profiles with high scale lambda and low scale
-- mu, the squared spacetime product has exponent
--
--   lambda^2 mu^2 * lambda^(-3) * lambda^(-2)
--     = mu^2 lambda^(-3)
--
-- after measuring space-time on the high profile's scale.  Relative to the
-- high profile energy lambda^(-1), this carries (mu/lambda)^2; relative to the
-- low profile energy mu^(-1), it carries (mu/lambda)^3.
--
-- This file formalises only exponent arithmetic.  The analytic passage from
-- smooth/localised profiles to Gallagher's H^{1/2} profile decomposition is a
-- separate theorem and remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

one two three four five : ℚ
one = 1ℚ
two = one + one
three = two + one
four = two + two
five = four + one

neg : ℚ → ℚ
neg x = 0ℚ - x

energyScalingExponent : ℚ
energyScalingExponent = neg one

mixedDefectAmplitudeExponent : ℚ
mixedDefectAmplitudeExponent = four

spaceJacobianExponent : ℚ
spaceJacobianExponent = neg three

timeJacobianExponent : ℚ
timeJacobianExponent = neg two

mixedDefectScalingExponent : ℚ
mixedDefectScalingExponent =
  mixedDefectAmplitudeExponent
  + spaceJacobianExponent
  + timeJacobianExponent

mixedDefectScalesLikeEnergy :
  mixedDefectScalingExponent ≡ energyScalingExponent
mixedDefectScalesLikeEnergy = solve []

-- High-scale normalisation of a two-profile product:
-- lambda^2 mu^2 * lambda^-3 * lambda^-2 = mu^2 lambda^-3.
highPowerInTwoProfileSpacetimeProduct : ℚ
highPowerInTwoProfileSpacetimeProduct = two - three - two

lowPowerInTwoProfileSpacetimeProduct : ℚ
lowPowerInTwoProfileSpacetimeProduct = two

highPowerIsMinusThree :
  highPowerInTwoProfileSpacetimeProduct ≡ neg three
highPowerIsMinusThree = solve []

-- Divide by high-profile energy lambda^-1: high exponent rises from -3 to -2,
-- giving (mu/lambda)^2.
highEnergyNormalisedHighPower : ℚ
highEnergyNormalisedHighPower =
  highPowerInTwoProfileSpacetimeProduct - energyScalingExponent

highEnergyNormalisedHighPowerIsMinusTwo :
  highEnergyNormalisedHighPower ≡ neg two
highEnergyNormalisedHighPowerIsMinusTwo = solve []

-- Divide by low-profile energy mu^-1: low exponent rises from +2 to +3,
-- giving (mu/lambda)^3.
lowEnergyNormalisedLowPower : ℚ
lowEnergyNormalisedLowPower =
  lowPowerInTwoProfileSpacetimeProduct - energyScalingExponent

lowEnergyNormalisedLowPowerIsThree :
  lowEnergyNormalisedLowPower ≡ three
lowEnergyNormalisedLowPowerIsThree = solve []

round237MixedDefectAndEnergyHaveSameNSScaling : Bool
round237MixedDefectAndEnergyHaveSameNSScaling = true

round237EnergyNormalisedDefectScaleInvariant : Bool
round237EnergyNormalisedDefectScaleInvariant = true

round237OrthogonalScaleCrossProfileGainIdentified : Bool
round237OrthogonalScaleCrossProfileGainIdentified = true

round237SmoothProfileDecouplingAnalyticTheoremClosed : Bool
round237SmoothProfileDecouplingAnalyticTheoremClosed = false

round237GallagherProfileDecouplingClosed : Bool
round237GallagherProfileDecouplingClosed = false

round237PackageAClosed : Bool
round237PackageAClosed = false

round237ClayPromotion : Bool
round237ClayPromotion = false

round237MixedDefectAndEnergyHaveSameNSScalingIsTrue :
  round237MixedDefectAndEnergyHaveSameNSScaling ≡ true
round237MixedDefectAndEnergyHaveSameNSScalingIsTrue = refl

round237GallagherProfileDecouplingClosedIsFalse :
  round237GallagherProfileDecouplingClosed ≡ false
round237GallagherProfileDecouplingClosedIsFalse = refl

round237PackageAClosedIsFalse : round237PackageAClosed ≡ false
round237PackageAClosedIsFalse = refl
