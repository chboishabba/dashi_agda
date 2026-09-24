{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTGeneralIsraelDECCompatibleShellExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- GENERAL STATIC ISRAEL SHELL WITH RATIONAL SQUARE ROOTS
--
-- For a timelike shell at fixed R, matching the induced metric uses shell
-- proper time and does NOT require f_in(R)=f_out(R) in the two coordinate
-- charts.  The static Israel formulas are
--
--   sigma = (sqrt(f_in)-sqrt(f_out)) / (4*pi*R)
--
--   P = 1/(8*pi) *
--       ( f'_out/(2 sqrt(f_out))
--       - f'_in /(2 sqrt(f_in))
--       + (sqrt(f_out)-sqrt(f_in))/R ).
--
-- Choose an exact rational-square fixture:
--
--   M = 1/4
--   R = 2
--   Lambda_out = 3/8       -> f_out(R)=1/4, sqrt=1/2
--   Lambda_in  = 21/64     -> f_in(R)=9/16, sqrt=3/4.
--
-- The exterior is static and outward-accelerating.
------------------------------------------------------------------------

mass : ℚ
mass = Int.+ 1 / 4

radius : ℚ
radius = Int.+ 2 / 1

lambdaOut : ℚ
lambdaOut = Int.+ 3 / 8

lambdaIn : ℚ
lambdaIn = Int.+ 21 / 64

sqrtFOut : ℚ
sqrtFOut = Int.+ 1 / 2

sqrtFIn : ℚ
sqrtFIn = Int.+ 3 / 4

fOutIsQuarter :
  Junction.fExterior radius mass lambdaOut ≡ Int.+ 1 / 4
fOutIsQuarter = solve []

fInIsNineSixteenths :
  Junction.fInterior radius lambdaIn ≡ Int.+ 9 / 16
fInIsNineSixteenths = solve []

sqrtFOutSquaresCorrectly :
  sqrtFOut * sqrtFOut ≡ Junction.fExterior radius mass lambdaOut
sqrtFOutSquaresCorrectly = solve []

sqrtFInSquaresCorrectly :
  sqrtFIn * sqrtFIn ≡ Junction.fInterior radius lambdaIn
sqrtFInSquaresCorrectly = solve []

exteriorAcceleration :
  ℚ
exteriorAcceleration =
  Junction.radialAcceleration radius mass lambdaOut

exteriorAccelerationIsThreeSixteenths :
  exteriorAcceleration ≡ Int.+ 3 / 16
exteriorAccelerationIsThreeSixteenths = solve []

------------------------------------------------------------------------
-- EXTRINSIC CURVATURE JUMPS
------------------------------------------------------------------------

kTauOut : ℚ
kTauOut =
  Junction.fExteriorPrime radius mass lambdaOut
    / ((Int.+ 2 / 1) * sqrtFOut)

kTauIn : ℚ
kTauIn =
  Junction.fInteriorPrime radius lambdaIn
    / ((Int.+ 2 / 1) * sqrtFIn)

kThetaOut : ℚ
kThetaOut = sqrtFOut / radius

kThetaIn : ℚ
kThetaIn = sqrtFIn / radius

kTauJump : ℚ
kTauJump = kTauOut - kTauIn

kThetaJump : ℚ
kThetaJump = kThetaOut - kThetaIn

kTauOutIsMinusThreeEighths :
  kTauOut ≡ - (Int.+ 3 / 8)
kTauOutIsMinusThreeEighths = solve []

kTauInIsMinusSevenTwentyFourths :
  kTauIn ≡ - (Int.+ 7 / 24)
kTauInIsMinusSevenTwentyFourths = solve []

kTauJumpIsMinusOneTwelfth :
  kTauJump ≡ - (Int.+ 1 / 12)
kTauJumpIsMinusOneTwelfth = solve []

kThetaJumpIsMinusOneEighth :
  kThetaJump ≡ - (Int.+ 1 / 8)
kThetaJumpIsMinusOneEighth = solve []

------------------------------------------------------------------------
-- RATIONALIZED ISRAEL SURFACE STRESS
--
-- Define the exact 8*pi-scaled quantities:
--
--   Sigma8 = 8*pi*sigma = 2(sqrt(f_in)-sqrt(f_out))/R
--   P8     = 8*pi*P     = [K_tau^tau] + [K_theta^theta].
--
-- For the fixture:
--
--   Sigma8 = 1/4
--   P8     = -5/24.
------------------------------------------------------------------------

surfaceSigma8Pi : ℚ
surfaceSigma8Pi =
  (Int.+ 2 / 1) * (sqrtFIn - sqrtFOut) / radius

surfacePressure8Pi : ℚ
surfacePressure8Pi =
  kTauJump + kThetaJump

surfaceSigma8PiIsQuarter :
  surfaceSigma8Pi ≡ Int.+ 1 / 4
surfaceSigma8PiIsQuarter = solve []

surfacePressure8PiIsMinusFiveTwentyFourths :
  surfacePressure8Pi ≡ - (Int.+ 5 / 24)
surfacePressure8PiIsMinusFiveTwentyFourths = solve []

------------------------------------------------------------------------
-- ENERGY CONDITIONS
--
-- Here |P8| = 5/24 and Sigma8 = 6/24.
--
--   NEC: Sigma8 + P8 = 1/24 > 0
--   WEC: Sigma8 > 0 and NEC
--   DEC: Sigma8 - |P8| = 1/24 > 0
--
-- So unlike the matched-lapse sigma=0 branch, this shell can satisfy the
-- dominant energy condition.
------------------------------------------------------------------------

surfaceNECMargin8Pi : ℚ
surfaceNECMargin8Pi =
  surfaceSigma8Pi + surfacePressure8Pi

surfaceDECMargin8Pi : ℚ
surfaceDECMargin8Pi =
  surfaceSigma8Pi - (Int.+ 5 / 24)

surfaceNECMarginIsOneTwentyFourth :
  surfaceNECMargin8Pi ≡ Int.+ 1 / 24
surfaceNECMarginIsOneTwentyFourth = solve []

surfaceDECMarginIsOneTwentyFourth :
  surfaceDECMargin8Pi ≡ Int.+ 1 / 24
surfaceDECMarginIsOneTwentyFourth = solve []

data EnergyConditionStatus : Set where
  necWecDecCompatible : EnergyConditionStatus

fixtureEnergyConditionStatus : EnergyConditionStatus
fixtureEnergyConditionStatus = necWecDecCompatible

record GeneralIsraelDECCompatibleShellWitness : Set where
  constructor general-israel-dec-compatible-shell-witness
  field
    exteriorLapse :
      Junction.fExterior radius mass lambdaOut ≡ Int.+ 1 / 4

    interiorLapse :
      Junction.fInterior radius lambdaIn ≡ Int.+ 9 / 16

    outwardAcceleration :
      exteriorAcceleration ≡ Int.+ 3 / 16

    sigma8Pi :
      surfaceSigma8Pi ≡ Int.+ 1 / 4

    pressure8Pi :
      surfacePressure8Pi ≡ - (Int.+ 5 / 24)

    necMargin :
      surfaceNECMargin8Pi ≡ Int.+ 1 / 24

    decMargin :
      surfaceDECMargin8Pi ≡ Int.+ 1 / 24

    energyConditionStatus :
      EnergyConditionStatus

open GeneralIsraelDECCompatibleShellWitness public

canonicalGeneralIsraelDECCompatibleShellWitness :
  GeneralIsraelDECCompatibleShellWitness
canonicalGeneralIsraelDECCompatibleShellWitness =
  general-israel-dec-compatible-shell-witness
    fOutIsQuarter
    fInIsNineSixteenths
    exteriorAccelerationIsThreeSixteenths
    surfaceSigma8PiIsQuarter
    surfacePressure8PiIsMinusFiveTwentyFourths
    surfaceNECMarginIsOneTwentyFourth
    surfaceDECMarginIsOneTwentyFourth
    necWecDecCompatible

record GeneralIsraelDECCompatibleShellBoundary : Set where
  constructor general-israel-dec-compatible-shell-boundary
  field
    coordinateLapseEqualityRequiredForGeneralIsraelShell : Bool
    positiveSurfaceEnergyDensityConstructed : Bool
    surfaceTensionConstructed : Bool
    outwardExteriorAccelerationConstructed : Bool
    nullEnergyConditionCompatible : Bool
    weakEnergyConditionCompatible : Bool
    dominantEnergyConditionCompatible : Bool
    negativeSurfaceEnergyRequired : Bool
    matchedLapseZeroSigmaBranchIsOnlyPossibleBranch : Bool

canonicalGeneralIsraelDECCompatibleShellBoundary :
  GeneralIsraelDECCompatibleShellBoundary
canonicalGeneralIsraelDECCompatibleShellBoundary =
  general-israel-dec-compatible-shell-boundary
    false true true true true true true false false
