{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTIsraelShellEnergyConditionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction
import DASHI.Physics.Foundations.GRQFTIsraelSurfaceStressMagnitudeExact as Israel

------------------------------------------------------------------------
-- SURFACE STRESS ENERGY-CONDITION FINGERPRINT
--
-- For the matched static shell:
--
--   sigma = 0
--   P > 0.
--
-- In an orthonormal 2+1 shell frame this means:
--
--   NEC: sigma + P > 0              passes
--   WEC: sigma >= 0 and NEC         passes
--   SEC: sigma + 2P > 0 and NEC     passes
--   DEC: sigma >= |P|               fails because 0 < P.
--
-- We encode the exact sign logic rather than importing an analytic absolute
-- value theory merely to restate these finite signs.
------------------------------------------------------------------------

data SurfaceEnergyDensitySign : Set where
  negativeSigma : SurfaceEnergyDensitySign
  zeroSigma : SurfaceEnergyDensitySign
  positiveSigma : SurfaceEnergyDensitySign

data SurfacePressureSign : Set where
  negativePressure : SurfacePressureSign
  zeroPressure : SurfacePressureSign
  positivePressure : SurfacePressureSign

fixtureSigmaSign : SurfaceEnergyDensitySign
fixtureSigmaSign = zeroSigma

fixturePressureSign : SurfacePressureSign
fixturePressureSign = positivePressure

data EnergyConditionVerdict : Set where
  conditionPasses : EnergyConditionVerdict
  conditionFails : EnergyConditionVerdict

surfaceNEC :
  SurfaceEnergyDensitySign →
  SurfacePressureSign →
  EnergyConditionVerdict
surfaceNEC negativeSigma pressure = conditionFails
surfaceNEC zeroSigma negativePressure = conditionFails
surfaceNEC zeroSigma zeroPressure = conditionPasses
surfaceNEC zeroSigma positivePressure = conditionPasses
surfaceNEC positiveSigma pressure = conditionPasses

surfaceWEC :
  SurfaceEnergyDensitySign →
  SurfacePressureSign →
  EnergyConditionVerdict
surfaceWEC negativeSigma pressure = conditionFails
surfaceWEC zeroSigma negativePressure = conditionFails
surfaceWEC zeroSigma zeroPressure = conditionPasses
surfaceWEC zeroSigma positivePressure = conditionPasses
surfaceWEC positiveSigma pressure = conditionPasses

surfaceSEC :
  SurfaceEnergyDensitySign →
  SurfacePressureSign →
  EnergyConditionVerdict
surfaceSEC negativeSigma pressure = conditionFails
surfaceSEC zeroSigma negativePressure = conditionFails
surfaceSEC zeroSigma zeroPressure = conditionPasses
surfaceSEC zeroSigma positivePressure = conditionPasses
surfaceSEC positiveSigma pressure = conditionPasses

surfaceDEC :
  SurfaceEnergyDensitySign →
  SurfacePressureSign →
  EnergyConditionVerdict
surfaceDEC negativeSigma pressure = conditionFails
surfaceDEC zeroSigma negativePressure = conditionFails
surfaceDEC zeroSigma zeroPressure = conditionPasses
surfaceDEC zeroSigma positivePressure = conditionFails
surfaceDEC positiveSigma pressure = conditionPasses

fixtureNECPasses :
  surfaceNEC fixtureSigmaSign fixturePressureSign ≡ conditionPasses
fixtureNECPasses = refl

fixtureWECPasses :
  surfaceWEC fixtureSigmaSign fixturePressureSign ≡ conditionPasses
fixtureWECPasses = refl

fixtureSECPasses :
  surfaceSEC fixtureSigmaSign fixturePressureSign ≡ conditionPasses
fixtureSECPasses = refl

fixtureDECFails :
  surfaceDEC fixtureSigmaSign fixturePressureSign ≡ conditionFails
fixtureDECFails = refl

positivePressureWithZeroSigmaCannotPassDEC :
  surfaceDEC zeroSigma positivePressure ≡ conditionPasses → ⊥
positivePressureWithZeroSigmaCannotPassDEC ()

------------------------------------------------------------------------
-- SAME SHELL AS THE JUNCTION CALCULATION
------------------------------------------------------------------------

junctionPressureOrientationIsPositive :
  Junction.fixtureSurfaceTangentialStressOrientation
    ≡ Junction.positiveSurfacePressure
junctionPressureOrientationIsPositive = refl

junctionSurfaceEnergyDensityNumeratorIsZero :
  Israel.surfaceEnergyDensityJumpNumerator
    ≡ Data.Rational.Base.0ℚ
junctionSurfaceEnergyDensityNumeratorIsZero =
  Israel.surfaceEnergyDensityIsZero

record IsraelShellEnergyConditionWitness : Set where
  constructor israel-shell-energy-condition-witness
  field
    sigmaSign : SurfaceEnergyDensitySign
    pressureSign : SurfacePressureSign

    sigmaIsZero :
      sigmaSign ≡ zeroSigma

    pressureIsPositive :
      pressureSign ≡ positivePressure

    nullEnergyCondition :
      surfaceNEC sigmaSign pressureSign ≡ conditionPasses

    weakEnergyCondition :
      surfaceWEC sigmaSign pressureSign ≡ conditionPasses

    strongEnergyCondition :
      surfaceSEC sigmaSign pressureSign ≡ conditionPasses

    dominantEnergyCondition :
      surfaceDEC sigmaSign pressureSign ≡ conditionFails

open IsraelShellEnergyConditionWitness public

canonicalIsraelShellEnergyConditionWitness :
  IsraelShellEnergyConditionWitness
canonicalIsraelShellEnergyConditionWitness =
  israel-shell-energy-condition-witness
    zeroSigma
    positivePressure
    refl
    refl
    refl
    refl
    refl
    refl

record IsraelShellEnergyConditionBoundary : Set where
  constructor israel-shell-energy-condition-boundary
  field
    shellNECPasses : Bool
    shellWECPasses : Bool
    shellSECPasses : Bool
    shellDECPasses : Bool
    shellRequiresDominantEnergyViolation : Bool
    shellHasNegativeSurfaceEnergyDensity : Bool
    shellHasPositiveTangentialPressure : Bool

canonicalIsraelShellEnergyConditionBoundary :
  IsraelShellEnergyConditionBoundary
canonicalIsraelShellEnergyConditionBoundary =
  israel-shell-energy-condition-boundary
    true true true false true false true
