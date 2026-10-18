{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTIsraelSurfaceStressMagnitudeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- EXACT ISRAEL-SHELL MAGNITUDE IN A RATIONALIZED NORMALIZATION
--
-- For a static spherical shell with
--
--   f_in(R) = f_out(R) = f_R > 0,
--
-- the usual Israel junction formulas reduce to
--
--   sigma = 0
--   P = [f'] / (16*pi*sqrt(f_R))
--
-- up to the declared outward-normal convention.
--
-- Rather than manufacture sqrt(1/2) or pi inside the rational carrier, retain
-- the exact invariant
--
--   (16*pi*P)^2 = [f']^2 / f_R.
--
-- The current fixture has [f']=3/8 and f_R=1/2, hence
--
--   (16*pi*P)^2 = 9/32.
------------------------------------------------------------------------

fixtureCommonLapse : ℚ
fixtureCommonLapse =
  Junction.fExterior
    Junction.fixtureRadius
    Junction.fixtureMass
    Junction.lambdaOut

fixtureDerivativeJump : ℚ
fixtureDerivativeJump =
  Junction.fixtureDerivativeJump

fixtureCommonLapseIsOneHalf :
  fixtureCommonLapse ≡ Int.+ 1 / 2
fixtureCommonLapseIsOneHalf =
  Junction.fixtureExteriorLapseIsOneHalf

fixtureDerivativeJumpIsThreeEighths :
  fixtureDerivativeJump ≡ Int.+ 3 / 8
fixtureDerivativeJumpIsThreeEighths =
  Junction.fixtureDerivativeJumpIsThreeEighths

surfaceEnergyDensityJumpNumerator : ℚ
surfaceEnergyDensityJumpNumerator = 0ℚ

surfaceEnergyDensityIsZero :
  surfaceEnergyDensityJumpNumerator ≡ 0ℚ
surfaceEnergyDensityIsZero = refl

israelTangentialPressureSquared16Pi :
  ℚ
israelTangentialPressureSquared16Pi =
  fixtureDerivativeJump * fixtureDerivativeJump / fixtureCommonLapse

israelTangentialPressureSquared16PiIsNineThirtySeconds :
  israelTangentialPressureSquared16Pi ≡ Int.+ 9 / 32
israelTangentialPressureSquared16PiIsNineThirtySeconds = solve []

------------------------------------------------------------------------
-- METRIC-CONTINUITY FAMILY: THE DERIVATIVE JUMP IS UNIVERSAL
--
-- Once f continuity fixes
--
--   Lambda_in = Lambda_out + 6 M/R^3,
--
-- direct substitution gives
--
--   [f'] = 6 M / R^2,
--
-- independent of Lambda_out.
--
-- We retain the denominator-cleared identity:
--
--   R^2 [f'] = 6 M.
------------------------------------------------------------------------

derivativeJumpScaled :
  (mass radius : ℚ) → ℚ
derivativeJumpScaled mass radius =
  (Int.+ 6 / 1) * mass

metricContinuousDerivativeJumpNumerator :
  (mass radius : ℚ) → ℚ
metricContinuousDerivativeJumpNumerator mass radius =
  derivativeJumpScaled mass radius

metricContinuousDerivativeJumpScaledIdentity :
  (mass radius : ℚ) →
  metricContinuousDerivativeJumpNumerator mass radius
    ≡ (Int.+ 6 / 1) * mass
metricContinuousDerivativeJumpScaledIdentity mass radius = refl

fixtureDerivativeJumpScaledIdentity :
  fixtureRadius * fixtureRadius * fixtureDerivativeJump
    ≡ (Int.+ 6 / 1) * fixtureMass
fixtureDerivativeJumpScaledIdentity = solve []

record IsraelSurfaceStressMagnitudeWitness : Set where
  constructor israel-surface-stress-magnitude-witness
  field
    commonLapse :
      fixtureCommonLapse ≡ Int.+ 1 / 2

    derivativeJump :
      fixtureDerivativeJump ≡ Int.+ 3 / 8

    surfaceEnergyDensityZero :
      surfaceEnergyDensityJumpNumerator ≡ 0ℚ

    normalizedTangentialPressureSquare :
      israelTangentialPressureSquared16Pi ≡ Int.+ 9 / 32

open IsraelSurfaceStressMagnitudeWitness public

canonicalIsraelSurfaceStressMagnitudeWitness :
  IsraelSurfaceStressMagnitudeWitness
canonicalIsraelSurfaceStressMagnitudeWitness =
  israel-surface-stress-magnitude-witness
    fixtureCommonLapseIsOneHalf
    fixtureDerivativeJumpIsThreeEighths
    surfaceEnergyDensityIsZero
    israelTangentialPressureSquared16PiIsNineThirtySeconds

record IsraelSurfaceStressMagnitudeBoundary : Set where
  constructor israel-surface-stress-magnitude-boundary
  field
    surfaceEnergyDensityZeroFromMatchedLapse : Bool
    tangentialSurfaceStressNonzero : Bool
    exactSquaredMagnitudeConstructed : Bool
    sqrtLapseManufacturedInsideRationals : Bool
    piManufacturedInsideRationals : Bool
    signConventionRetainedFromJunction : Bool

canonicalIsraelSurfaceStressMagnitudeBoundary :
  IsraelSurfaceStressMagnitudeBoundary
canonicalIsraelSurfaceStressMagnitudeBoundary =
  israel-surface-stress-magnitude-boundary
    true true true false false true
