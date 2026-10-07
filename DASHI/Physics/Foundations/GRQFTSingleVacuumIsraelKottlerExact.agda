{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design

------------------------------------------------------------------------
-- SINGLE-VACUUM ISRAEL / KOTTLER BRANCH
--
-- A two-level vacuum potential is not required by the static geometry.  Use the
-- SAME cosmological amplitude on both sides.  Different lapse roots are then
-- supplied by the positive exterior mass term.
--
-- With rational lapse roots x=sqrt(f_in), y=sqrt(f_out), equal Lambda implies
--
--   M = R (x^2-y^2)/2.
--
-- The denominator-cleared common vacuum amplitude is
--
--   Lambda R^3 = 3 R (1-x^2),
--
-- and substitution of M makes the exterior lapse equation return exactly the
-- same quantity.  This reduces the source search from TWO vacuum amplitudes to
-- ONE source-native vacuum coefficient plus geometric admissibility.
------------------------------------------------------------------------

half : ℚ
half = Int.+ 1 / 2

three : ℚ
three = Int.+ 3 / 1

sameVacuumMass : ℚ → ℚ → ℚ → ℚ
sameVacuumMass radius x y =
  half * radius * (x * x - y * y)

sameVacuumScaledAmplitude : ℚ → ℚ → ℚ
sameVacuumScaledAmplitude radius x =
  three * radius * (Int.+ 1 / 1 - x * x)

sameVacuumExteriorScaledAmplitude : ℚ → ℚ → ℚ → ℚ
sameVacuumExteriorScaledAmplitude radius x y =
  three * radius * (Int.+ 1 / 1 - y * y)
  - (Int.+ 6 / 1) * sameVacuumMass radius x y

sameVacuumAmplitude : ℚ → ℚ → ℚ
sameVacuumAmplitude radius x =
  Design.lambdaInFromSquareLapse radius x

sameScaledAmplitudeOnBothSides :
  ∀ radius x y →
  sameVacuumExteriorScaledAmplitude radius x y
  ≡ sameVacuumScaledAmplitude radius x
sameScaledAmplitudeOnBothSides radius x y =
  solve (radius ∷ x ∷ y ∷ [])

sameVacuumOutwardScaled : ℚ → ℚ → ℚ → ℚ
sameVacuumOutwardScaled radius x y =
  Design.outwardAccelerationScaled
    (sameVacuumMass radius x y) radius y

sameVacuumNECDECMargin : ℚ → ℚ → ℚ → ℚ
sameVacuumNECDECMargin radius x y =
  Design.necDecMarginCleared
    (sameVacuumMass radius x y) radius x y

sameVacuumSECViolationMargin : ℚ → ℚ → ℚ → ℚ
sameVacuumSECViolationMargin radius x y =
  Design.secViolationMarginCleared
    (sameVacuumMass radius x y) radius x y

sameVacuumPressureTensionMargin : ℚ → ℚ → ℚ → ℚ
sameVacuumPressureTensionMargin radius x y =
  Design.pressureTensionMarginCleared
    (sameVacuumMass radius x y) radius x y

------------------------------------------------------------------------
-- Exact strong fixture.
--
-- R=2, x=2/3, y=3/5 gives
--   Lambda_in = Lambda_out = 5/12,
--   M = 19/225 > 0,
--   R^2 a_out = 77/75 > 0,
--   8*pi*sigma = 1/15,
--   8*pi*P = -2/45,
--   NEC/DEC cleared margin = 8/225 > 0,
--   SEC-violation cleared margin = 4/225 > 0.
------------------------------------------------------------------------

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureX : ℚ
fixtureX = Int.+ 2 / 3

fixtureY : ℚ
fixtureY = Int.+ 3 / 5

fixtureMass : ℚ
fixtureMass = sameVacuumMass fixtureRadius fixtureX fixtureY

fixtureLambda : ℚ
fixtureLambda = sameVacuumAmplitude fixtureRadius fixtureX

fixtureLambdaIsFiveTwelfths :
  fixtureLambda ≡ Int.+ 5 / 12
fixtureLambdaIsFiveTwelfths = solve []

fixtureMassIsNineteenTwoTwentyFifths :
  fixtureMass ≡ Int.+ 19 / 225
fixtureMassIsNineteenTwoTwentyFifths = solve []

fixtureExteriorLambdaIsSame :
  Design.lambdaOutFromSquareLapse fixtureMass fixtureRadius fixtureY
  ≡ fixtureLambda
fixtureExteriorLambdaIsSame = solve []

fixtureOutwardScaledIsSeventySevenSeventyFifths :
  sameVacuumOutwardScaled fixtureRadius fixtureX fixtureY
  ≡ Int.+ 77 / 75
fixtureOutwardScaledIsSeventySevenSeventyFifths = solve []

fixtureSigmaIsOneFifteenth :
  Design.surfaceSigma8 fixtureRadius fixtureX fixtureY
  ≡ Int.+ 1 / 15
fixtureSigmaIsOneFifteenth = solve []

fixturePressureIsMinusTwoFortyFifths :
  Design.surfacePressure8 fixtureMass fixtureRadius fixtureX fixtureY
  ≡ - (Int.+ 2 / 45)
fixturePressureIsMinusTwoFortyFifths = solve []

fixtureNECDECMarginIsEightTwoTwentyFifths :
  sameVacuumNECDECMargin fixtureRadius fixtureX fixtureY
  ≡ Int.+ 8 / 225
fixtureNECDECMarginIsEightTwoTwentyFifths = solve []

fixtureSECViolationMarginIsFourTwoTwentyFifths :
  sameVacuumSECViolationMargin fixtureRadius fixtureX fixtureY
  ≡ Int.+ 4 / 225
fixtureSECViolationMarginIsFourTwoTwentyFifths = solve []

fixturePressureTensionMarginIsSixteenTwoTwentyFifths :
  sameVacuumPressureTensionMargin fixtureRadius fixtureX fixtureY
  ≡ Int.+ 16 / 225
fixturePressureTensionMarginIsSixteenTwoTwentyFifths = solve []

record SingleVacuumIsraelKottlerBoundary : Set where
  constructor single-vacuum-israel-kottler-boundary
  field
    sameVacuumOnInteriorAndExterior : Bool
    positiveMetricMassFixture : Bool
    outwardExteriorAccelerationFixture : Bool
    positiveSurfaceEnergyFixture : Bool
    surfaceTensionFixture : Bool
    necDecCompatibleFixture : Bool
    strongEnergyConditionViolatedFixture : Bool
    twoDifferentVacuumAmplitudesRequired : Bool
    oneSourceVacuumAmplitudeCanFeedBothRegions : Bool

canonicalSingleVacuumIsraelKottlerBoundary :
  SingleVacuumIsraelKottlerBoundary
canonicalSingleVacuumIsraelKottlerBoundary =
  single-vacuum-israel-kottler-boundary
    true true true true true true true false true
