{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSchwarzschildDeSitterExteriorEscapeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTPositiveDensityExteriorRepulsionNoGoExact as NoGo

------------------------------------------------------------------------
-- NON-VACUUM EXTERIOR ESCAPE: SCHWARZSCHILD-DE SITTER / KOTTLER SIGN CUT
--
-- The standard weak-field radial acceleration associated with a positive-mass
-- Kottler exterior has the schematic form
--
--   a_r = - M/r^2 + Lambda*r/3
--
-- in G=c=1 units.  Positive M is inward; positive Lambda is outward.
--
-- This file is an exact rational sign/magnitude fixture for that external
-- competition.  It does not claim SI calibration or that the finite interior
-- has already been junction-matched to this exterior.
------------------------------------------------------------------------

kottlerRadialAcceleration :
  (mass radius lambda : ℚ) → ℚ
kottlerRadialAcceleration mass radius lambda =
  0ℚ - mass / (radius * radius)
  + lambda * radius / (Int.+ 3 / 1)

surfaceMass : ℚ
surfaceMass = TOV.outerMassTarget

probeRadius : ℚ
probeRadius = Int.+ 2 / 1

exteriorLambda : ℚ
exteriorLambda = Int.+ 3 / 4

massAttractionTerm : ℚ
massAttractionTerm =
  surfaceMass / (probeRadius * probeRadius)

lambdaRepulsionTerm : ℚ
lambdaRepulsionTerm =
  exteriorLambda * probeRadius / (Int.+ 3 / 1)

massAttractionTermIsOneSixteenth :
  massAttractionTerm ≡ Int.+ 1 / 16
massAttractionTermIsOneSixteenth = solve []

lambdaRepulsionTermIsOneHalf :
  lambdaRepulsionTerm ≡ Int.+ 1 / 2
lambdaRepulsionTermIsOneHalf = solve []

kottlerAccelerationIsSevenSixteenthsOutward :
  kottlerRadialAcceleration surfaceMass probeRadius exteriorLambda
    ≡ Int.+ 7 / 16
kottlerAccelerationIsSevenSixteenthsOutward = solve []

------------------------------------------------------------------------
-- EXACT THRESHOLD
--
-- Outward acceleration begins when
--
--   Lambda*r/3 > M/r^2
--   <=> Lambda*r^3 > 3M.
--
-- For the fixture M=1/4, r=2:
--
--   Lambda_threshold = 3M/r^3 = 3/32.
------------------------------------------------------------------------

lambdaThreshold :
  (mass radius : ℚ) → ℚ
lambdaThreshold mass radius =
  (Int.+ 3 / 1) * mass
    / (radius * radius * radius)

fixtureLambdaThresholdIsThreeThirtySeconds :
  lambdaThreshold surfaceMass probeRadius
    ≡ Int.+ 3 / 32
fixtureLambdaThresholdIsThreeThirtySeconds = solve []

exteriorLambdaExceedsThresholdByTwentyOneThirtySeconds :
  exteriorLambda - lambdaThreshold surfaceMass probeRadius
    ≡ Int.+ 21 / 32
exteriorLambdaExceedsThresholdByTwentyOneThirtySeconds = solve []

------------------------------------------------------------------------
-- ESCAPE-ROUTE WITNESS
------------------------------------------------------------------------

data ExteriorAccelerationOrientation : Set where
  inwardExterior : ExteriorAccelerationOrientation
  balancedExterior : ExteriorAccelerationOrientation
  outwardExterior : ExteriorAccelerationOrientation

fixtureKottlerOrientation : ExteriorAccelerationOrientation
fixtureKottlerOrientation = outwardExterior

record PositiveMassNonVacuumExteriorRepulsionWitness : Set where
  constructor positive-mass-nonvacuum-exterior-repulsion-witness
  field
    metricMass :
      surfaceMass ≡ Int.+ 1 / 4

    lambda :
      exteriorLambda ≡ Int.+ 3 / 4

    threshold :
      lambdaThreshold surfaceMass probeRadius
        ≡ Int.+ 3 / 32

    radialAcceleration :
      kottlerRadialAcceleration surfaceMass probeRadius exteriorLambda
        ≡ Int.+ 7 / 16

    orientation :
      ExteriorAccelerationOrientation
    orientationOutward :
      orientation ≡ outwardExterior

    escapeRoute :
      NoGo.ExteriorRepulsionEscapeRoute
    escapeRouteIsNonVacuumExterior :
      escapeRoute ≡ NoGo.nonVacuumExteriorStress

open PositiveMassNonVacuumExteriorRepulsionWitness public

canonicalPositiveMassNonVacuumExteriorRepulsionWitness :
  PositiveMassNonVacuumExteriorRepulsionWitness
canonicalPositiveMassNonVacuumExteriorRepulsionWitness =
  positive-mass-nonvacuum-exterior-repulsion-witness
    refl
    refl
    fixtureLambdaThresholdIsThreeThirtySeconds
    kottlerAccelerationIsSevenSixteenthsOutward
    outwardExterior
    refl
    NoGo.nonVacuumExteriorStress
    refl

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record SchwarzschildDeSitterEscapeBoundary : Set where
  constructor schwarzschild-de-sitter-escape-boundary
  field
    positiveMetricMassRetained : Bool
    positiveGCompatible : Bool
    negativeMassRequired : Bool
    nonVacuumExteriorRequired : Bool
    exactOutwardRationalFixtureConstructed : Bool
    lambdaThresholdConstructed : Bool
    interiorExteriorJunctionSolved : Bool
    SIPhysicalMagnitudeCalibrated : Bool

canonicalSchwarzschildDeSitterEscapeBoundary :
  SchwarzschildDeSitterEscapeBoundary
canonicalSchwarzschildDeSitterEscapeBoundary =
  schwarzschild-de-sitter-escape-boundary
    true true false true true true false false
