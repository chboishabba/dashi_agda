{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTParameterizedRepulsiveJunctionDesignExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact as Window
import DASHI.Physics.Foundations.GRQFTIsraelSurfaceStressMagnitudeExact as Israel
import DASHI.Physics.Foundations.GRQFTDeSitterKottlerJunctionExact as Junction

------------------------------------------------------------------------
-- PARAMETERIZED DESIGN FAMILY
--
-- Write the radius as
--
--   R = 3M + delta.
--
-- Then the Kottler repulsion/static midpoint has:
--
--   outward margin = (3/2) delta
--   static margin  = (3/2) delta
--   window width   = 3 delta.
--
-- Thus delta is the exact design slack beyond the photon-sphere-like R=3M
-- threshold of this sign problem.
------------------------------------------------------------------------

radiusFromGap :
  (mass gap : ℚ) → ℚ
radiusFromGap mass gap =
  (Int.+ 3 / 1) * mass + gap

gapMidpointOutwardMargin :
  (mass gap : ℚ) →
  Window.outwardAccelerationMargin
    mass
    (Window.scaledLambdaMidpoint mass (radiusFromGap mass gap))
  ≡ (Int.+ 3 / 2) * gap
gapMidpointOutwardMargin mass gap =
  solve (mass ∷ gap ∷ [])

gapMidpointStaticMargin :
  (mass gap : ℚ) →
  Window.staticPatchMargin
    mass
    (radiusFromGap mass gap)
    (Window.scaledLambdaMidpoint mass (radiusFromGap mass gap))
  ≡ (Int.+ 3 / 2) * gap
gapMidpointStaticMargin mass gap =
  solve (mass ∷ gap ∷ [])

gapWindowWidth :
  (mass gap : ℚ) →
  Window.windowWidth mass (radiusFromGap mass gap)
    ≡ (Int.+ 3 / 1) * gap
gapWindowWidth mass gap =
  solve (mass ∷ gap ∷ [])

------------------------------------------------------------------------
-- JUNCTION-SHELL COST
--
-- Metric continuity fixes the derivative jump independently of exterior
-- Lambda:
--
--   [f'] = 6M/R^2.
--
-- The denominator-cleared shell-cost identity is therefore
--
--   R^2 [f'] = 6M.
------------------------------------------------------------------------

junctionDerivativeJumpScaledCost :
  (mass gap : ℚ) → ℚ
junctionDerivativeJumpScaledCost mass gap =
  (Int.+ 6 / 1) * mass

junctionDerivativeJumpScaledCostIdentity :
  (mass gap : ℚ) →
  junctionDerivativeJumpScaledCost mass gap
    ≡ (Int.+ 6 / 1) * mass
junctionDerivativeJumpScaledCostIdentity mass gap = refl

------------------------------------------------------------------------
-- EXACT FIXTURE AS ONE MEMBER OF THE FAMILY
------------------------------------------------------------------------

fixtureMass : ℚ
fixtureMass = Int.+ 1 / 4

fixtureGap : ℚ
fixtureGap = Int.+ 5 / 4

fixtureRadiusFromGapIsTwo :
  radiusFromGap fixtureMass fixtureGap
    ≡ Int.+ 2 / 1
fixtureRadiusFromGapIsTwo = solve []

fixtureOutwardMarginIsFifteenEighths :
  Window.outwardAccelerationMargin
    fixtureMass
    (Window.scaledLambdaMidpoint
      fixtureMass
      (radiusFromGap fixtureMass fixtureGap))
  ≡ Int.+ 15 / 8
fixtureOutwardMarginIsFifteenEighths = solve []

fixtureStaticMarginIsFifteenEighths :
  Window.staticPatchMargin
    fixtureMass
    (radiusFromGap fixtureMass fixtureGap)
    (Window.scaledLambdaMidpoint
      fixtureMass
      (radiusFromGap fixtureMass fixtureGap))
  ≡ Int.+ 15 / 8
fixtureStaticMarginIsFifteenEighths = solve []

fixtureShellScaledDerivativeCostIsThreeHalves :
  junctionDerivativeJumpScaledCost fixtureMass fixtureGap
    ≡ Int.+ 3 / 2
fixtureShellScaledDerivativeCostIsThreeHalves = solve []

------------------------------------------------------------------------
-- COMPOSED FAMILY WITNESS
------------------------------------------------------------------------

record ParameterizedRepulsiveJunctionDesign
    (mass gap : ℚ) : Set where
  constructor parameterized-repulsive-junction-design
  field
    radius : ℚ
    radiusDefinition :
      radius ≡ radiusFromGap mass gap

    midpointScaledLambda : ℚ
    midpointLambdaDefinition :
      midpointScaledLambda
        ≡ Window.scaledLambdaMidpoint mass radius

    outwardMargin :
      Window.outwardAccelerationMargin mass midpointScaledLambda
        ≡ (Int.+ 3 / 2) * gap

    staticMargin :
      Window.staticPatchMargin mass radius midpointScaledLambda
        ≡ (Int.+ 3 / 2) * gap

    windowWidth :
      Window.windowWidth mass radius
        ≡ (Int.+ 3 / 1) * gap

    shellDerivativeScaledCost :
      junctionDerivativeJumpScaledCost mass gap
        ≡ (Int.+ 6 / 1) * mass

open ParameterizedRepulsiveJunctionDesign public

parameterizedRepulsiveJunctionDesign :
  (mass gap : ℚ) →
  ParameterizedRepulsiveJunctionDesign mass gap
parameterizedRepulsiveJunctionDesign mass gap =
  parameterized-repulsive-junction-design
    (radiusFromGap mass gap)
    refl
    (Window.scaledLambdaMidpoint mass (radiusFromGap mass gap))
    refl
    (gapMidpointOutwardMargin mass gap)
    (gapMidpointStaticMargin mass gap)
    (gapWindowWidth mass gap)
    refl

record ParameterizedRepulsiveJunctionDesignBoundary : Set where
  constructor parameterized-repulsive-junction-design-boundary
  field
    radiusGapParameterizationConstructed : Bool
    outwardMarginLinearInGap : Bool
    staticMarginLinearInGap : Bool
    lambdaWindowWidthLinearInGap : Bool
    shellDerivativeCostIndependentOfLambdaOut : Bool
    exactFixtureRecovered : Bool
    positivityRequiresGapPositiveWitness : Bool
    exactIsraelSquaredMagnitudeAvailableForFixture : Bool

canonicalParameterizedRepulsiveJunctionDesignBoundary :
  ParameterizedRepulsiveJunctionDesignBoundary
canonicalParameterizedRepulsiveJunctionDesignBoundary =
  parameterized-repulsive-junction-design-boundary
    true true true true true true true true
