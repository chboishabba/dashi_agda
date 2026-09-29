{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTIsraelShellEnergyConditionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (0ℚ)

import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction
import DASHI.Physics.Foundations.GRQFTIsraelSurfaceStressMagnitudeExact as Israel

------------------------------------------------------------------------
-- EXACT SHELL ENERGY-CONDITION FINGERPRINT
--
-- For the matched static shell already derived:
--
--   sigma = 0
--   P > 0.
--
-- Therefore in the orthonormal 2+1 shell frame:
--
--   NEC: sigma + P = P > 0                  passes
--   WEC: sigma = 0 and NEC                  passes
--   SEC: sigma + 2P = 2P > 0 and NEC        passes
--   DEC: sigma >= |P| becomes 0 >= P         fails.
--
-- This module deliberately classifies only THIS exact sign/magnitude regime.
-- It does not pretend signs alone classify arbitrary shells.
------------------------------------------------------------------------

data ExactShellClass : Set where
  zeroSigmaPositivePressureShell : ExactShellClass

data EnergyConditionVerdict : Set where
  conditionPasses : EnergyConditionVerdict
  conditionFails : EnergyConditionVerdict

shellNEC :
  ExactShellClass → EnergyConditionVerdict
shellNEC zeroSigmaPositivePressureShell = conditionPasses

shellWEC :
  ExactShellClass → EnergyConditionVerdict
shellWEC zeroSigmaPositivePressureShell = conditionPasses

shellSEC :
  ExactShellClass → EnergyConditionVerdict
shellSEC zeroSigmaPositivePressureShell = conditionPasses

shellDEC :
  ExactShellClass → EnergyConditionVerdict
shellDEC zeroSigmaPositivePressureShell = conditionFails

fixtureShellClass : ExactShellClass
fixtureShellClass = zeroSigmaPositivePressureShell

fixtureNECPasses :
  shellNEC fixtureShellClass ≡ conditionPasses
fixtureNECPasses = refl

fixtureWECPasses :
  shellWEC fixtureShellClass ≡ conditionPasses
fixtureWECPasses = refl

fixtureSECPasses :
  shellSEC fixtureShellClass ≡ conditionPasses
fixtureSECPasses = refl

fixtureDECFails :
  shellDEC fixtureShellClass ≡ conditionFails
fixtureDECFails = refl

fixtureDECCannotPass :
  shellDEC fixtureShellClass ≡ conditionPasses → ⊥
fixtureDECCannotPass ()

------------------------------------------------------------------------
-- SAME SHELL AS THE JUNCTION CALCULATION
------------------------------------------------------------------------

junctionPressureOrientationIsPositive :
  Junction.fixtureSurfaceTangentialStressOrientation
    ≡ Junction.positiveSurfacePressure
junctionPressureOrientationIsPositive = refl

junctionSurfaceEnergyDensityNumeratorIsZero :
  Israel.surfaceEnergyDensityJumpNumerator ≡ 0ℚ
junctionSurfaceEnergyDensityNumeratorIsZero =
  Israel.surfaceEnergyDensityIsZero

record IsraelShellEnergyConditionWitness : Set where
  constructor israel-shell-energy-condition-witness
  field
    shellClass : ExactShellClass

    nullEnergyCondition :
      shellNEC shellClass ≡ conditionPasses

    weakEnergyCondition :
      shellWEC shellClass ≡ conditionPasses

    strongEnergyCondition :
      shellSEC shellClass ≡ conditionPasses

    dominantEnergyCondition :
      shellDEC shellClass ≡ conditionFails

open IsraelShellEnergyConditionWitness public

canonicalIsraelShellEnergyConditionWitness :
  IsraelShellEnergyConditionWitness
canonicalIsraelShellEnergyConditionWitness =
  israel-shell-energy-condition-witness
    zeroSigmaPositivePressureShell
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
    genericSignOnlyEnergyConditionClassifierClaimed : Bool

canonicalIsraelShellEnergyConditionBoundary :
  IsraelShellEnergyConditionBoundary
canonicalIsraelShellEnergyConditionBoundary =
  israel-shell-energy-condition-boundary
    true true true false true false true false
