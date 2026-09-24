{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTStressDerivedRepulsiveJunctionFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTVacuumStressLambdaCompilerExact as Vacuum
import DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact as Window
import DASHI.Physics.Foundations.GRQFTParameterizedRepulsiveJunctionDesignExact as Design

------------------------------------------------------------------------
-- STRESS-DERIVED JUNCTION FAMILY
--
-- Choose mass M and radius R.  The Kottler midpoint stress amplitude is
--
--   lambda_out = L_mid / R^3
--              = (3/2)(R-M) / R^3.
--
-- Metric continuity then fixes
--
--   lambda_in = lambda_out + 6M/R^3
--             = (3/2)(R+3M) / R^3.
--
-- Thus both interior and exterior cosmological terms lie on the SAME
-- vacuum-stress ray and are fixed algebraically by M,R once the midpoint design
-- is selected.
------------------------------------------------------------------------

exteriorStressAmplitudeNumerator :
  (mass radius : ℚ) → ℚ
exteriorStressAmplitudeNumerator mass radius =
  Window.scaledLambdaMidpoint mass radius

interiorStressAmplitudeNumerator :
  (mass radius : ℚ) → ℚ
interiorStressAmplitudeNumerator mass radius =
  exteriorStressAmplitudeNumerator mass radius
  + (Int.+ 6 / 1) * mass

exteriorStressAmplitude :
  (mass radius : ℚ) → ℚ
exteriorStressAmplitude mass radius =
  exteriorStressAmplitudeNumerator mass radius
    / (radius * radius * radius)

interiorStressAmplitude :
  (mass radius : ℚ) → ℚ
interiorStressAmplitude mass radius =
  interiorStressAmplitudeNumerator mass radius
    / (radius * radius * radius)

interiorAmplitudeNumeratorIdentity :
  (mass radius : ℚ) →
  interiorStressAmplitudeNumerator mass radius
    ≡ (Int.+ 3 / 2)
        * (radius + (Int.+ 3 / 1) * mass)
interiorAmplitudeNumeratorIdentity mass radius =
  solve (mass ∷ radius ∷ [])

junctionAmplitudeJumpNumerator :
  (mass radius : ℚ) →
  interiorStressAmplitudeNumerator mass radius
    - exteriorStressAmplitudeNumerator mass radius
  ≡ (Int.+ 6 / 1) * mass
junctionAmplitudeJumpNumerator mass radius =
  solve (mass ∷ radius ∷ [])

------------------------------------------------------------------------
-- STRESS TENSORS DERIVED FROM THOSE AMPLITUDES
------------------------------------------------------------------------

exteriorStressFromGeometry :
  (mass radius : ℚ) →
  Vacuum.Stress.RationalTensor4
exteriorStressFromGeometry mass radius =
  Vacuum.vacuumStressAt (exteriorStressAmplitude mass radius)

interiorStressFromGeometry :
  (mass radius : ℚ) →
  Vacuum.Stress.RationalTensor4
interiorStressFromGeometry mass radius =
  Vacuum.vacuumStressAt (interiorStressAmplitude mass radius)

------------------------------------------------------------------------
-- FIXTURE RECOVERY AT M=1/4, R=2 FOR MIDPOINT DESIGN
------------------------------------------------------------------------

fixtureMass : ℚ
fixtureMass = Int.+ 1 / 4

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureExteriorAmplitudeIsTwentyOneSixtyFourths :
  exteriorStressAmplitude fixtureMass fixtureRadius
    ≡ Int.+ 21 / 64
fixtureExteriorAmplitudeIsTwentyOneSixtyFourths = solve []

fixtureInteriorAmplitudeIsThirtyThreeSixtyFourths :
  interiorStressAmplitude fixtureMass fixtureRadius
    ≡ Int.+ 33 / 64
fixtureInteriorAmplitudeIsThirtyThreeSixtyFourths = solve []

fixtureAmplitudeJumpIsThreeSixteenths :
  interiorStressAmplitude fixtureMass fixtureRadius
    - exteriorStressAmplitude fixtureMass fixtureRadius
  ≡ Int.+ 3 / 16
fixtureAmplitudeJumpIsThreeSixteenths = solve []

record StressDerivedRepulsiveJunctionFamilyWitness
    (mass radius : ℚ) : Set where
  constructor stress-derived-repulsive-junction-family-witness
  field
    exteriorAmplitude : ℚ
    exteriorAmplitudeDefinition :
      exteriorAmplitude ≡ exteriorStressAmplitude mass radius

    interiorAmplitude : ℚ
    interiorAmplitudeDefinition :
      interiorAmplitude ≡ interiorStressAmplitude mass radius

    jumpNumerator :
      interiorStressAmplitudeNumerator mass radius
        - exteriorStressAmplitudeNumerator mass radius
      ≡ (Int.+ 6 / 1) * mass

    sameExteriorStressRay :
      exteriorStressFromGeometry mass radius
        ≡ Vacuum.vacuumStressAt exteriorAmplitude

    sameInteriorStressRay :
      interiorStressFromGeometry mass radius
        ≡ Vacuum.vacuumStressAt interiorAmplitude

open StressDerivedRepulsiveJunctionFamilyWitness public

stressDerivedRepulsiveJunctionFamily :
  (mass radius : ℚ) →
  StressDerivedRepulsiveJunctionFamilyWitness mass radius
stressDerivedRepulsiveJunctionFamily mass radius =
  stress-derived-repulsive-junction-family-witness
    (exteriorStressAmplitude mass radius)
    refl
    (interiorStressAmplitude mass radius)
    refl
    (junctionAmplitudeJumpNumerator mass radius)
    refl
    refl

record StressDerivedRepulsiveJunctionFamilyBoundary : Set where
  constructor stress-derived-repulsive-junction-family-boundary
  field
    exteriorLambdaIsStressAmplitude : Bool
    interiorLambdaIsStressAmplitude : Bool
    bothUseSameVacuumStressRay : Bool
    geometryFixesAmplitudeJump : Bool
    midpointGeometryFixesBothAmplitudes : Bool
    qftAmplitudeDynamicsDerived : Bool
    physicalScaleCalibrated : Bool

canonicalStressDerivedRepulsiveJunctionFamilyBoundary :
  StressDerivedRepulsiveJunctionFamilyBoundary
canonicalStressDerivedRepulsiveJunctionFamilyBoundary =
  stress-derived-repulsive-junction-family-boundary
    true true true true true false false
