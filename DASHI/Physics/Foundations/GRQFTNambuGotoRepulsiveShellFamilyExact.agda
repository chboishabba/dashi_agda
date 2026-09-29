{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveShellFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design

------------------------------------------------------------------------
-- EXACT ONE-PARAMETER NAMBU-GOTO-LIKE REPULSIVE SHELL FAMILY
--
-- Fix
--
--   x = sqrt(f_in)  = 3/4
--   y = sqrt(f_out) = 1/2
--
-- and impose the domain-wall mass law
--
--   3 M x = R(x-y).
--
-- This gives simply
--
--   M = R/9.
--
-- The cleared NEC/DEC margin is exactly zero, i.e. the shell lies on the
-- P=-sigma domain-wall boundary.  SEC is violated and the exterior
-- acceleration margin is positive for positive R.
------------------------------------------------------------------------

x : ℚ
x = Int.+ 3 / 4

y : ℚ
y = Int.+ 1 / 2

massAtRadius :
  ℚ → ℚ
massAtRadius radius =
  radius / (Int.+ 9 / 1)

domainWallMassLaw :
  (radius : ℚ) →
  (Int.+ 3 / 1) * massAtRadius radius * x
    ≡ radius * (x - y)
domainWallMassLaw radius =
  solve (radius ∷ [])

pressureTensionMarginFamily :
  (radius : ℚ) →
  Design.pressureTensionMarginCleared
    (massAtRadius radius) radius x y
  ≡ (Int.+ 3 / 16) * radius
pressureTensionMarginFamily radius =
  solve (radius ∷ [])

necDecSaturationFamily :
  (radius : ℚ) →
  Design.necDecMarginCleared
    (massAtRadius radius) radius x y
  ≡ 0ℚ
necDecSaturationFamily radius =
  solve (radius ∷ [])

secViolationMarginFamily :
  (radius : ℚ) →
  Design.secViolationMarginCleared
    (massAtRadius radius) radius x y
  ≡ (Int.+ 3 / 32) * radius
secViolationMarginFamily radius =
  solve (radius ∷ [])

outwardAccelerationMarginFamily :
  (radius : ℚ) →
  Design.outwardAccelerationScaled
    (massAtRadius radius) radius y
  ≡ (Int.+ 5 / 12) * radius
outwardAccelerationMarginFamily radius =
  solve (radius ∷ [])

kottlerGapFamily :
  (radius : ℚ) →
  radius - (Int.+ 3 / 1) * massAtRadius radius
  ≡ (Int.+ 2 / 3) * radius
kottlerGapFamily radius =
  solve (radius ∷ [])

------------------------------------------------------------------------
-- Vacuum-stress amplitude scalings:
--
--   Lambda_in  R^2 = 21/16
--   Lambda_out R^2 = 19/12.
--
-- These are represented as scaled amplitudes so no variable-denominator
-- theorem is manufactured in the Agda rational-ring lane.
------------------------------------------------------------------------

scaledInteriorLambda : ℚ
scaledInteriorLambda = Int.+ 21 / 16

scaledExteriorLambda : ℚ
scaledExteriorLambda = Int.+ 19 / 12

record NambuGotoRepulsiveShellFamilyWitness
    (radius : ℚ) : Set where
  constructor nambu-goto-repulsive-shell-family-witness
  field
    mass : ℚ
    massDefinition :
      mass ≡ massAtRadius radius

    massLaw :
      (Int.+ 3 / 1) * mass * x
        ≡ radius * (x - y)

    pressureTension :
      Design.pressureTensionMarginCleared mass radius x y
        ≡ (Int.+ 3 / 16) * radius

    necDecSaturated :
      Design.necDecMarginCleared mass radius x y
        ≡ 0ℚ

    secViolation :
      Design.secViolationMarginCleared mass radius x y
        ≡ (Int.+ 3 / 32) * radius

    outwardAcceleration :
      Design.outwardAccelerationScaled mass radius y
        ≡ (Int.+ 5 / 12) * radius

    staticWindowGap :
      radius - (Int.+ 3 / 1) * mass
        ≡ (Int.+ 2 / 3) * radius

open NambuGotoRepulsiveShellFamilyWitness public

nambuGotoRepulsiveShellFamily :
  (radius : ℚ) →
  NambuGotoRepulsiveShellFamilyWitness radius
nambuGotoRepulsiveShellFamily radius =
  nambu-goto-repulsive-shell-family-witness
    (massAtRadius radius)
    refl
    (domainWallMassLaw radius)
    (pressureTensionMarginFamily radius)
    (necDecSaturationFamily radius)
    (secViolationMarginFamily radius)
    (outwardAccelerationMarginFamily radius)
    (kottlerGapFamily radius)

------------------------------------------------------------------------
-- Exact R=2 member
------------------------------------------------------------------------

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureMass :
  massAtRadius fixtureRadius ≡ Int.+ 2 / 9
fixtureMass = solve []

fixturePressureTensionMargin :
  Design.pressureTensionMarginCleared
    (massAtRadius fixtureRadius) fixtureRadius x y
  ≡ Int.+ 3 / 8
fixturePressureTensionMargin = solve []

fixtureSECViolationMargin :
  Design.secViolationMarginCleared
    (massAtRadius fixtureRadius) fixtureRadius x y
  ≡ Int.+ 3 / 16
fixtureSECViolationMargin = solve []

fixtureOutwardMargin :
  Design.outwardAccelerationScaled
    (massAtRadius fixtureRadius) fixtureRadius y
  ≡ Int.+ 5 / 6
fixtureOutwardMargin = solve []

fixtureLambdaIn :
  Design.lambdaInFromSquareLapse fixtureRadius x
    ≡ Int.+ 21 / 64
fixtureLambdaIn = solve []

fixtureLambdaOut :
  Design.lambdaOutFromSquareLapse
    (massAtRadius fixtureRadius) fixtureRadius y
    ≡ Int.+ 19 / 48
fixtureLambdaOut = solve []

fixtureRadialAcceleration :
  ((Int.+ 5 / 12) * fixtureRadius)
    / (fixtureRadius * fixtureRadius)
  ≡ Int.+ 5 / 24
fixtureRadialAcceleration = solve []

record NambuGotoRepulsiveShellFamilyBoundary : Set where
  constructor nambu-goto-repulsive-shell-family-boundary
  field
    positiveMassCoefficient : Bool
    domainWallMassLawConstructed : Bool
    pressureIsTensionBranch : Bool
    necDecSaturated : Bool
    secViolatedForPositiveRadius : Bool
    outwardAccelerationForPositiveRadius : Bool
    rGreaterThanThreeMForPositiveRadius : Bool
    negativeMetricMassRequired : Bool
    negativeNewtonGRequired : Bool

canonicalNambuGotoRepulsiveShellFamilyBoundary :
  NambuGotoRepulsiveShellFamilyBoundary
canonicalNambuGotoRepulsiveShellFamilyBoundary =
  nambu-goto-repulsive-shell-family-boundary
    true true true true true true true false false
