{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTBalancedDECRepulsiveShellFamilyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTRationalSquareIsraelDesignExact as Design

------------------------------------------------------------------------
-- ONE-PARAMETER EXACT DEC-COMPATIBLE FAMILY
--
-- Fix rational lapse roots
--
--   x = 3/4
--   y = 1/2
--
-- and choose the balanced mass law from the Lean general theorem:
--
--   M = R (x-y)(xy+2)/(6x) = 19 R / 144.
--
-- Then every denominator-cleared design margin is linear in R.
------------------------------------------------------------------------

x : ℚ
x = Int.+ 3 / 4

y : ℚ
y = Int.+ 1 / 2

massAtRadius :
  ℚ → ℚ
massAtRadius radius =
  (Int.+ 19 / 144) * radius

pressureTensionMarginFamily :
  (radius : ℚ) →
  Design.pressureTensionMarginCleared
    (massAtRadius radius) radius x y
  ≡ (Int.+ 9 / 64) * radius
pressureTensionMarginFamily radius =
  solve (radius ∷ [])

necDecMarginFamily :
  (radius : ℚ) →
  Design.necDecMarginCleared
    (massAtRadius radius) radius x y
  ≡ (Int.+ 3 / 64) * radius
necDecMarginFamily radius =
  solve (radius ∷ [])

secViolationMarginFamily :
  (radius : ℚ) →
  Design.secViolationMarginCleared
    (massAtRadius radius) radius x y
  ≡ (Int.+ 3 / 64) * radius
secViolationMarginFamily radius =
  solve (radius ∷ [])

outwardAccelerationMarginFamily :
  (radius : ℚ) →
  Design.outwardAccelerationScaled
    (massAtRadius radius) radius y
  ≡ (Int.+ 17 / 48) * radius
outwardAccelerationMarginFamily radius =
  solve (radius ∷ [])

------------------------------------------------------------------------
-- Compactness ratio is fixed:
--
--   3M = 19R/48
--
-- so the Kottler-window gap from R=3M is
--
--   R-3M = 29R/48.
------------------------------------------------------------------------

threeMassAtRadius :
  (radius : ℚ) →
  (Int.+ 3 / 1) * massAtRadius radius
  ≡ (Int.+ 19 / 48) * radius
threeMassAtRadius radius =
  solve (radius ∷ [])

radiusMinusThreeMass :
  (radius : ℚ) →
  radius - (Int.+ 3 / 1) * massAtRadius radius
  ≡ (Int.+ 29 / 48) * radius
radiusMinusThreeMass radius =
  solve (radius ∷ [])

record BalancedDECRepulsiveShellFamilyWitness
    (radius : ℚ) : Set where
  constructor balanced-dec-repulsive-shell-family-witness
  field
    mass : ℚ
    massDefinition :
      mass ≡ massAtRadius radius

    pressureTensionMargin :
      Design.pressureTensionMarginCleared mass radius x y
        ≡ (Int.+ 9 / 64) * radius

    necDecMargin :
      Design.necDecMarginCleared mass radius x y
        ≡ (Int.+ 3 / 64) * radius

    secViolationMargin :
      Design.secViolationMarginCleared mass radius x y
        ≡ (Int.+ 3 / 64) * radius

    outwardMargin :
      Design.outwardAccelerationScaled mass radius y
        ≡ (Int.+ 17 / 48) * radius

    kottlerGap :
      radius - (Int.+ 3 / 1) * mass
        ≡ (Int.+ 29 / 48) * radius

open BalancedDECRepulsiveShellFamilyWitness public

balancedDECRepulsiveShellFamily :
  (radius : ℚ) →
  BalancedDECRepulsiveShellFamilyWitness radius
balancedDECRepulsiveShellFamily radius =
  balanced-dec-repulsive-shell-family-witness
    (massAtRadius radius)
    refl
    (pressureTensionMarginFamily radius)
    (necDecMarginFamily radius)
    (secViolationMarginFamily radius)
    (outwardAccelerationMarginFamily radius)
    (radiusMinusThreeMass radius)

------------------------------------------------------------------------
-- Exact R=2 member
------------------------------------------------------------------------

fixtureRadius : ℚ
fixtureRadius = Int.+ 2 / 1

fixtureMass :
  massAtRadius fixtureRadius ≡ Int.+ 19 / 72
fixtureMass = solve []

fixturePressureMargin :
  Design.pressureTensionMarginCleared
    (massAtRadius fixtureRadius) fixtureRadius x y
  ≡ Int.+ 9 / 32
fixturePressureMargin = solve []

fixtureNECDECMargin :
  Design.necDecMarginCleared
    (massAtRadius fixtureRadius) fixtureRadius x y
  ≡ Int.+ 3 / 32
fixtureNECDECMargin = solve []

fixtureSECViolationMargin :
  Design.secViolationMarginCleared
    (massAtRadius fixtureRadius) fixtureRadius x y
  ≡ Int.+ 3 / 32
fixtureSECViolationMargin = solve []

fixtureOutwardMargin :
  Design.outwardAccelerationScaled
    (massAtRadius fixtureRadius) fixtureRadius y
  ≡ Int.+ 17 / 24
fixtureOutwardMargin = solve []

record BalancedDECRepulsiveShellFamilyBoundary : Set where
  constructor balanced-dec-repulsive-shell-family-boundary
  field
    positiveMassCoefficient : Bool
    pressureTensionMarginLinearPositiveCoefficient : Bool
    necDecMarginLinearPositiveCoefficient : Bool
    secViolationMarginLinearPositiveCoefficient : Bool
    outwardAccelerationMarginLinearPositiveCoefficient : Bool
    rMinusThreeMLinearPositiveCoefficient : Bool
    positivityForPositiveRadiusRequiresOnlyOrderTransport : Bool

canonicalBalancedDECRepulsiveShellFamilyBoundary :
  BalancedDECRepulsiveShellFamilyBoundary
canonicalBalancedDECRepulsiveShellFamilyBoundary =
  balanced-dec-repulsive-shell-family-boundary
    true true true true true true true
