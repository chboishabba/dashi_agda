module DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- This module proves the finite path version of the difference-quotient to
-- diffusion step.  A displacement is decomposed into vector increments d_j.
-- The endpoint difference is their sum, and finite Cauchy--Schwarz gives
--
--   |sum_j d_j|^2
--     <= (# path steps) sum_j |d_j|^2.
--
-- The proof reuses the normalized finite-filter Jensen carrier with unit
-- square-root weights, so all three vector coordinates and all constants are
-- checked.  This is the exact discrete path estimate underlying the continuum
-- fundamental-theorem-of-calculus bound.  Passing to an actual torus segment,
-- identifying d_j with spatial derivatives, and obtaining the scale-uniform
-- annular coefficient remain analytic interfaces.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFilterIncrementJensenExact as Jensen

unitWeightSamples : List Gram.Vec3 → List Jensen.FilterIncrementSample
unitWeightSamples [] = []
unitWeightSamples (increment ∷ increments) =
  Jensen.filterIncrementSample 1ℚ increment
  ∷ unitWeightSamples increments

pathEndpointDifference : List Gram.Vec3 → Gram.Vec3
pathEndpointDifference increments =
  Jensen.sumWeightedIncrement (unitWeightSamples increments)

pathStepCount : List Gram.Vec3 → ℚ
pathStepCount increments =
  Jensen.totalFilterWeight (unitWeightSamples increments)

pathGradientEnergy : List Gram.Vec3 → ℚ
pathGradientEnergy increments =
  Jensen.weightedIncrementEnergy (unitWeightSamples increments)

finitePathDifferenceBelowGradientEnergy :
  ∀ increments →
  Gram.normSquared (pathEndpointDifference increments)
  ≤ pathStepCount increments * pathGradientEnergy increments
finitePathDifferenceBelowGradientEnergy increments =
  Jensen.finiteFilterIncrementJensen (unitWeightSamples increments)

record FinitePathDifferenceAuthorityBoundary : Set where
  constructor finitePathDifferenceAuthorityBoundary
  field
    vectorPathCauchyEstimateProved : Set
    allThreeCoordinatesIncluded : Set
    torusSegmentPartitionConstructed : Set
    pathIncrementsIdentifiedWithGradient : Set
    annularScaleUniformCoefficientProduced : Set

canonicalFinitePathDifferenceAuthorityBoundary :
  FinitePathDifferenceAuthorityBoundary
canonicalFinitePathDifferenceAuthorityBoundary =
  finitePathDifferenceAuthorityBoundary ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
