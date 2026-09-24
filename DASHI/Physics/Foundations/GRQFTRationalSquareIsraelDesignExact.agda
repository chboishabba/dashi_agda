{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- RATIONAL-SQUARE ISRAEL DESIGN FAMILY
--
-- Parameterize the shell by
--
--   x = sqrt(f_in(R))
--   y = sqrt(f_out(R))
--
-- with rational x,y.  The corresponding de Sitter/Kottler amplitudes are
--
--   lambda_in  = 3(1-x^2)/R^2
--   lambda_out = 3(1-2M/R-y^2)/R^2.
--
-- The exterior radial acceleration satisfies
--
--   R^2 a_out = R(1-y^2)-3M.
--
-- For x>y>0, define d=x-y.  The exact 8*pi-scaled shell quantities are
--
--   Sigma8 = 2d/R
--
--   P8 = - d(2xy+1)/(Rxy) + 3M/(R^2 y).
--
-- Clearing the positive geometric denominators exposes simple design margins.
------------------------------------------------------------------------

lambdaInFromSquareLapse :
  (radius x : ℚ) → ℚ
lambdaInFromSquareLapse radius x =
  (Int.+ 3 / 1) * (Int.+ 1 / 1 - x * x)
    / (radius * radius)

lambdaOutFromSquareLapse :
  (mass radius y : ℚ) → ℚ
lambdaOutFromSquareLapse mass radius y =
  (Int.+ 3 / 1)
    * (Int.+ 1 / 1
       - (Int.+ 2 / 1) * mass / radius
       - y * y)
    / (radius * radius)

outwardAccelerationScaled :
  (mass radius y : ℚ) → ℚ
outwardAccelerationScaled mass radius y =
  radius * (Int.+ 1 / 1 - y * y)
  - (Int.+ 3 / 1) * mass

surfaceGap :
  (x y : ℚ) → ℚ
surfaceGap x y = x - y

surfaceSigma8 :
  (radius x y : ℚ) → ℚ
surfaceSigma8 radius x y =
  (Int.+ 2 / 1) * surfaceGap x y / radius

surfacePressure8 :
  (mass radius x y : ℚ) → ℚ
surfacePressure8 mass radius x y =
  - (surfaceGap x y
      * ((Int.+ 2 / 1) * x * y + (Int.+ 1 / 1)))
      / (radius * x * y)
  + (Int.+ 3 / 1) * mass / (radius * radius * y)

------------------------------------------------------------------------
-- DENOMINATOR-CLEARED MARGINS
------------------------------------------------------------------------

pressureTensionMarginCleared :
  (mass radius x y : ℚ) → ℚ
pressureTensionMarginCleared mass radius x y =
  radius * surfaceGap x y
    * ((Int.+ 2 / 1) * x * y + (Int.+ 1 / 1))
  - (Int.+ 3 / 1) * mass * x

necDecMarginCleared :
  (mass radius x y : ℚ) → ℚ
necDecMarginCleared mass radius x y =
  (Int.+ 3 / 1) * mass * x
  - radius * surfaceGap x y

secViolationMarginCleared :
  (mass radius x y : ℚ) → ℚ
secViolationMarginCleared mass radius x y =
  radius * surfaceGap x y * (x * y + (Int.+ 1 / 1))
  - (Int.+ 3 / 1) * mass * x

------------------------------------------------------------------------
-- ALGEBRAIC IDENTITIES
--
-- P8 * R^2*x*y is minus the tension margin.
------------------------------------------------------------------------

pressureClearedIdentity :
  (mass radius x y : ℚ) →
  surfacePressure8 mass radius x y
    * (radius * radius * x * y)
  ≡ - (pressureTensionMarginCleared mass radius x y)
pressureClearedIdentity mass radius x y =
  solve (mass ∷ radius ∷ x ∷ y ∷ [])

------------------------------------------------------------------------
-- (Sigma8 + P8) * R^2*x*y = NEC/DEC margin.
------------------------------------------------------------------------

necClearedIdentity :
  (mass radius x y : ℚ) →
  (surfaceSigma8 radius x y
    + surfacePressure8 mass radius x y)
    * (radius * radius * x * y)
  ≡ necDecMarginCleared mass radius x y
necClearedIdentity mass radius x y =
  solve (mass ∷ radius ∷ x ∷ y ∷ [])

------------------------------------------------------------------------
-- -(Sigma8 + 2P8) * R^2*x*y / 2 is the SEC-violation margin.
-- Equivalently:
--
--   (Sigma8 + 2P8) * R^2*x*y
--     = -2 * secViolationMarginCleared.
------------------------------------------------------------------------

secClearedIdentity :
  (mass radius x y : ℚ) →
  (surfaceSigma8 radius x y
    + (Int.+ 2 / 1) * surfacePressure8 mass radius x y)
    * (radius * radius * x * y)
  ≡ - ((Int.+ 2 / 1) * secViolationMarginCleared mass radius x y)
secClearedIdentity mass radius x y =
  solve (mass ∷ radius ∷ x ∷ y ∷ [])

------------------------------------------------------------------------
-- FIXTURE RECOVERY
------------------------------------------------------------------------

fixtureMass : ℚ
fixtureMass = Int.+ 1 / 4

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureX : ℚ
fixtureX = Int.+ 3 / 4

fixtureY : ℚ
fixtureY = Int.+ 1 / 2

fixtureLambdaIn :
  lambdaInFromSquareLapse fixtureRadius fixtureX
    ≡ Int.+ 21 / 64
fixtureLambdaIn = solve []

fixtureLambdaOut :
  lambdaOutFromSquareLapse fixtureMass fixtureRadius fixtureY
    ≡ Int.+ 3 / 8
fixtureLambdaOut = solve []

fixtureOutwardAccelerationScaled :
  outwardAccelerationScaled fixtureMass fixtureRadius fixtureY
    ≡ Int.+ 3 / 4
fixtureOutwardAccelerationScaled = solve []

fixturePressureTensionMargin :
  pressureTensionMarginCleared
    fixtureMass fixtureRadius fixtureX fixtureY
  ≡ Int.+ 21 / 64
fixturePressureTensionMargin = solve []

fixtureNECDECMargin :
  necDecMarginCleared
    fixtureMass fixtureRadius fixtureX fixtureY
  ≡ Int.+ 1 / 16
fixtureNECDECMargin = solve []

fixtureSECViolationMargin :
  secViolationMarginCleared
    fixtureMass fixtureRadius fixtureX fixtureY
  ≡ Int.+ 1 / 4
fixtureSECViolationMargin = solve []

record RationalSquareIsraelDesignBoundary : Set where
  constructor rational-square-israel-design-boundary
  field
    vacuumAmplitudesDerivedFromSquareLapses : Bool
    outwardAccelerationHasClearedPolynomialMargin : Bool
    pressureTensionHasClearedPolynomialMargin : Bool
    necDecHasClearedPolynomialMargin : Bool
    secViolationHasClearedPolynomialMargin : Bool
    exactDECCompatibleFixtureRecovered : Bool
    orderTheoremsRequirePositiveRadiusAndLapseRoots : Bool

canonicalRationalSquareIsraelDesignBoundary :
  RationalSquareIsraelDesignBoundary
canonicalRationalSquareIsraelDesignBoundary =
  rational-square-israel-design-boundary
    true true true true true true true
