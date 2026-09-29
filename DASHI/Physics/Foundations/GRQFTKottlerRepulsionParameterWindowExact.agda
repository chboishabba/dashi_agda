{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- PARAMETER WINDOW FOR POSITIVE-MASS OUTWARD KOTTLER ACCELERATION
--
-- Avoid variable rational denominators by using the scaled coordinate
--
--   L = Lambda R^3.
--
-- Then:
--
--   outward acceleration  <=>  L > 3M
--   static patch f(R)>0   <=>  L < 3R - 6M.
--
-- Therefore a nonempty window exists exactly when
--
--   3M < 3R - 6M
--   <=> R > 3M.
--
-- The midpoint choice
--
--   L_mid = (3/2)(R-M)
--
-- makes both margins equal:
--
--   L_mid - 3M
--   = 3R - 6M - L_mid
--   = (3/2)(R-3M).
------------------------------------------------------------------------

scaledLambdaMidpoint :
  (mass radius : ℚ) → ℚ
scaledLambdaMidpoint mass radius =
  (Int.+ 3 / 2) * (radius - mass)

outwardAccelerationMargin :
  (mass scaledLambda : ℚ) → ℚ
outwardAccelerationMargin mass scaledLambda =
  scaledLambda - (Int.+ 3 / 1) * mass

staticPatchMargin :
  (mass radius scaledLambda : ℚ) → ℚ
staticPatchMargin mass radius scaledLambda =
  (Int.+ 3 / 1) * radius
  - (Int.+ 6 / 1) * mass
  - scaledLambda

midpointOutwardMarginIdentity :
  (mass radius : ℚ) →
  outwardAccelerationMargin mass (scaledLambdaMidpoint mass radius)
    ≡ (Int.+ 3 / 2) * (radius - (Int.+ 3 / 1) * mass)
midpointOutwardMarginIdentity mass radius =
  solve (mass ∷ radius ∷ [])

midpointStaticMarginIdentity :
  (mass radius : ℚ) →
  staticPatchMargin mass radius (scaledLambdaMidpoint mass radius)
    ≡ (Int.+ 3 / 2) * (radius - (Int.+ 3 / 1) * mass)
midpointStaticMarginIdentity mass radius =
  solve (mass ∷ radius ∷ [])

windowWidth :
  (mass radius : ℚ) → ℚ
windowWidth mass radius =
  ((Int.+ 3 / 1) * radius - (Int.+ 6 / 1) * mass)
  - (Int.+ 3 / 1) * mass

windowWidthIdentity :
  (mass radius : ℚ) →
  windowWidth mass radius
    ≡ (Int.+ 3 / 1) * (radius - (Int.+ 3 / 1) * mass)
windowWidthIdentity mass radius =
  solve (mass ∷ radius ∷ [])

------------------------------------------------------------------------
-- EXACT FIXTURE FROM THE JUNCTION CONSTRUCTION
------------------------------------------------------------------------

fixtureMass : ℚ
fixtureMass = Int.+ 1 / 4

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureScaledLambda :
  ℚ
fixtureScaledLambda =
  scaledLambdaMidpoint fixtureMass fixtureRadius

fixtureScaledLambdaIsTwentyOneEighths :
  fixtureScaledLambda ≡ Int.+ 21 / 8
fixtureScaledLambdaIsTwentyOneEighths = solve []

fixtureOutwardMargin :
  outwardAccelerationMargin fixtureMass fixtureScaledLambda
    ≡ Int.+ 15 / 8
fixtureOutwardMargin = solve []

fixtureStaticMargin :
  staticPatchMargin fixtureMass fixtureRadius fixtureScaledLambda
    ≡ Int.+ 15 / 8
fixtureStaticMargin = solve []

fixtureWindowWidth :
  windowWidth fixtureMass fixtureRadius
    ≡ Int.+ 15 / 4
fixtureWindowWidth = solve []

------------------------------------------------------------------------
-- Translate the midpoint scaled Lambda back for the exact fixture:
--
--   Lambda_mid = L_mid / R^3 = (21/8)/8 = 21/64.
--
-- This differs from the earlier convenient junction value 3/16; both lie in
-- the allowed window.  The point here is the family theorem, not one preferred
-- value.
------------------------------------------------------------------------

fixtureMidpointLambda : ℚ
fixtureMidpointLambda =
  fixtureScaledLambda / (fixtureRadius * fixtureRadius * fixtureRadius)

fixtureMidpointLambdaIsTwentyOneSixtyFourths :
  fixtureMidpointLambda ≡ Int.+ 21 / 64
fixtureMidpointLambdaIsTwentyOneSixtyFourths = solve []

record KottlerRepulsionParameterWindowWitness : Set where
  constructor kottler-repulsion-parameter-window-witness
  field
    mass : ℚ
    radius : ℚ

    midpointScaledLambda : ℚ
    midpointDefinition :
      midpointScaledLambda ≡ scaledLambdaMidpoint mass radius

    outwardMargin :
      outwardAccelerationMargin mass midpointScaledLambda
        ≡ (Int.+ 3 / 2) * (radius - (Int.+ 3 / 1) * mass)

    staticMargin :
      staticPatchMargin mass radius midpointScaledLambda
        ≡ (Int.+ 3 / 2) * (radius - (Int.+ 3 / 1) * mass)

    exactWindowWidth :
      windowWidth mass radius
        ≡ (Int.+ 3 / 1) * (radius - (Int.+ 3 / 1) * mass)

open KottlerRepulsionParameterWindowWitness public

kottlerRepulsionParameterWindow :
  (mass radius : ℚ) →
  KottlerRepulsionParameterWindowWitness
kottlerRepulsionParameterWindow mass radius =
  kottler-repulsion-parameter-window-witness
    mass
    radius
    (scaledLambdaMidpoint mass radius)
    refl
    (midpointOutwardMarginIdentity mass radius)
    (midpointStaticMarginIdentity mass radius)
    (windowWidthIdentity mass radius)

record KottlerRepulsionParameterWindowBoundary : Set where
  constructor kottler-repulsion-parameter-window-boundary
  field
    lowerScaledLambdaBoundIsThreeM : Bool
    upperScaledLambdaBoundIsThreeRMinusSixM : Bool
    nonemptyWindowControlledByRGreaterThanThreeM : Bool
    midpointMarginsEqual : Bool
    positiveMassCompatible : Bool
    negativeMassRequired : Bool
    inequalityOrderProofStillExternalToRingIdentity : Bool

canonicalKottlerRepulsionParameterWindowBoundary :
  KottlerRepulsionParameterWindowBoundary
canonicalKottlerRepulsionParameterWindowBoundary =
  kottler-repulsion-parameter-window-boundary
    true true true true true false true
