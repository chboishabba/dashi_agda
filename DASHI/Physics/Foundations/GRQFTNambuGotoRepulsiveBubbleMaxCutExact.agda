{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTCMP119NambuGotoRepulsiveExteriorCompilerExact as CMP
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveShellFamilyExact as Shell
import DASHI.Physics.Foundations.GRQFTNambuGotoTwoVacuumPotentialExact as Potential
import DASHI.Physics.Foundations.GRQFTNambuGotoSurfaceActionExact as Surface

------------------------------------------------------------------------
-- STRONGEST CURRENT CONSTRUCTIVE REPULSIVE-BUBBLE CANDIDATE
--
-- At R=2:
--
--   M             = 2/9 > 0
--   Lambda_in     = 21/64
--   Lambda_out    = 19/48
--   a_out         = 5/24 > 0
--   8*pi*sigma    = 1/4
--   8*pi*P        = -1/4
--
-- The same vacuum-stress tensor shape supplies both Lambda sectors by scalar
-- amplitude.  An explicit asymmetric double-well has those two vacuum energies.
-- A positive-tension Nambu-Goto surface source supplies P=-sigma.
--
-- Conditional only on the existing normalized CMP119 tensor payment, all
-- tensor transport is compiler-owned.  What is NOT yet proved is that the
-- source-native CMP119/YM action dynamically generates this scalar potential
-- and surface action.
------------------------------------------------------------------------

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureMass : ℚ
fixtureMass = Int.+ 2 / 9

fixtureInteriorLambda : ℚ
fixtureInteriorLambda = Int.+ 21 / 64

fixtureExteriorLambda : ℚ
fixtureExteriorLambda = Int.+ 19 / 48

fixtureOutwardAcceleration : ℚ
fixtureOutwardAcceleration = Int.+ 5 / 24

record NambuGotoRepulsiveBubbleCandidate
    {StressTensor : Set}
    (evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor)
    (cmp119Stress : StressTensor)
    (normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress) : Set where
  constructor nambu-goto-repulsive-bubble-candidate
  field
    shellFamily :
      Shell.NambuGotoRepulsiveShellFamilyWitness fixtureRadius

    twoVacuumPotential :
      Potential.NambuGotoTwoVacuumPotentialWitness

    surfaceSource :
      Surface.NambuGotoSurfaceSource

    cmp119Compiler :
      CMP.CMP119NambuGotoRepulsiveExteriorCompiler
        evaluator cmp119Stress normalized

    massValue :
      Shell.massAtRadius fixtureRadius ≡ fixtureMass

    interiorLambdaValue :
      Shell.Design.lambdaInFromSquareLapse fixtureRadius Shell.x
        ≡ fixtureInteriorLambda

    exteriorLambdaValue :
      Shell.Design.lambdaOutFromSquareLapse
        (Shell.massAtRadius fixtureRadius) fixtureRadius Shell.y
        ≡ fixtureExteriorLambda

    potentialInteriorMatchesGeometry :
      Potential.nambuVacuumPotential Potential.interiorField
        ≡ fixtureInteriorLambda

    potentialExteriorMatchesGeometry :
      Potential.nambuVacuumPotential Potential.exteriorField
        ≡ fixtureExteriorLambda

    surfaceEnergyPositive :
      Surface.surfaceSigma8Pi Surface.fixtureSurfaceSource
        ≡ Int.+ 1 / 4

    surfacePressureIsTension :
      Surface.surfacePressure8Pi Surface.fixtureSurfaceSource
        ≡ - (Int.+ 1 / 4)

    outwardAcceleration :
      ((Int.+ 5 / 12) * fixtureRadius)
        / (fixtureRadius * fixtureRadius)
      ≡ fixtureOutwardAcceleration

    interiorStressTransport :
      (a b : Flat.Axis4) →
      CMP.interiorStress a b
        ≡ CMP.Vacuum.scaledCMP119Tensor
            CMP.interiorAmplitude evaluator cmp119Stress a b

    exteriorStressTransport :
      (a b : Flat.Axis4) →
      CMP.exteriorStress a b
        ≡ CMP.Vacuum.scaledCMP119Tensor
            CMP.exteriorAmplitude evaluator cmp119Stress a b

open NambuGotoRepulsiveBubbleCandidate public

nambuGotoRepulsiveBubbleCandidate :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  (normalized :
    Stress.NormalizedCrossSectorStressInstance
      StressTensor evaluator cmp119Stress) →
  NambuGotoRepulsiveBubbleCandidate
    evaluator cmp119Stress normalized
nambuGotoRepulsiveBubbleCandidate normalized =
  nambu-goto-repulsive-bubble-candidate
    (Shell.nambuGotoRepulsiveShellFamily fixtureRadius)
    Potential.canonicalNambuGotoTwoVacuumPotentialWitness
    Surface.fixtureSurfaceSource
    (CMP.cmp119NambuGotoRepulsiveExteriorCompiler normalized)
    Shell.fixtureMass
    Shell.fixtureLambdaIn
    Shell.fixtureLambdaOut
    Potential.interiorEnergy
    Potential.exteriorEnergy
    Surface.fixtureSurfaceSigma
    Surface.fixtureSurfacePressure
    Shell.fixtureRadialAcceleration
    (CMP.cmp119CompilesNambuInteriorStress normalized)
    (CMP.cmp119CompilesNambuExteriorStress normalized)

record NambuGotoRepulsiveBubbleMaxCutBoundary : Set where
  constructor nambu-goto-repulsive-bubble-max-cut-boundary
  field
    positiveMetricMass : Bool
    positiveNewtonGCompatible : Bool
    outwardExteriorAcceleration : Bool
    positiveSurfaceEnergy : Bool
    nambuGotoEquationOfState : Bool
    necWecDecCompatible : Bool
    strongEnergyConditionViolated : Bool
    sameTensorRayFeedsInteriorExterior : Bool
    twoVacuumPotentialConstructed : Bool
    sourceNativeCMP119PotentialCouplingDerived : Bool
    finiteThicknessWallDerived : Bool
    SIUnitsCalibrated : Bool

canonicalNambuGotoRepulsiveBubbleMaxCutBoundary :
  NambuGotoRepulsiveBubbleMaxCutBoundary
canonicalNambuGotoRepulsiveBubbleMaxCutBoundary =
  nambu-goto-repulsive-bubble-max-cut-boundary
    true true true true true true true true true false false false
