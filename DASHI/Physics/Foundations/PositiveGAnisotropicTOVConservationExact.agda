{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGAnisotropicTOVConservationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Integer.Base as Int
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.PositiveGActiveStressWeakFieldMetricExact as Weak

------------------------------------------------------------------------
-- ANISOTROPIC STATIC CONSERVATION AUDIT
--
-- In a static spherically symmetric chart, local stress conservation has the
-- anisotropic TOV shape
--
--   p_r' + (rho + p_r) Phi' - 2 (p_t - p_r) / r = 0.
--
-- We encode the exact algebraic residual.  This does not claim the full
-- Einstein/TOV system has been solved; it identifies the precise obstruction
-- for the current two-zone constant-pressure fixture.
------------------------------------------------------------------------

anisotropicConservationResidual :
  ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
anisotropicConservationResidual rho pr pt prPrime phiPrime inverseRadius =
  prPrime
  + (rho + pr) * phiPrime
  - (1ℚ + 1ℚ) * (pt - pr) * inverseRadius

boundaryRho : ℚ
boundaryRho = 1ℚ

boundaryPr : ℚ
boundaryPr = 0ℚ

boundaryPt : ℚ
boundaryPt = - 1ℚ

boundaryInverseRadius : ℚ
boundaryInverseRadius = 1ℚ

boundaryConstantPrPrime : ℚ
boundaryConstantPrPrime = 0ℚ

requiredBoundaryPhiPrime : ℚ
requiredBoundaryPhiPrime = - (Int.+ 2 / Int.+ 1)

boundaryConstantPressureRequiresPhiPrimeMinusTwo :
  anisotropicConservationResidual
    boundaryRho boundaryPr boundaryPt boundaryConstantPrPrime
    requiredBoundaryPhiPrime boundaryInverseRadius
  ≡ 0ℚ
boundaryConstantPressureRequiresPhiPrimeMinusTwo = solve []

weakFieldBoundaryPhiPrime : ℚ
weakFieldBoundaryPhiPrime = Weak.exteriorSurfaceRadialDerivative

weakFieldBoundaryResidual : ℚ
weakFieldBoundaryResidual =
  anisotropicConservationResidual
    boundaryRho boundaryPr boundaryPt boundaryConstantPrPrime
    weakFieldBoundaryPhiPrime boundaryInverseRadius

weakFieldBoundaryResidualIsFiveThirds :
  weakFieldBoundaryResidual ≡ Int.+ 5 / Int.+ 3
weakFieldBoundaryResidualIsFiveThirds = solve []

data ConservedStaticSolutionStatus : Set where
  conservedStaticSolution : ConservedStaticSolutionStatus
  conservationResidualNonzero : ConservedStaticSolutionStatus

currentTwoZoneFixtureStatus : ConservedStaticSolutionStatus
currentTwoZoneFixtureStatus = conservationResidualNonzero

currentTwoZoneFixtureIsNotFullConservedStaticSolution : Bool
currentTwoZoneFixtureIsNotFullConservedStaticSolution = true

record AnisotropicTOVConservationBoundary : Set where
  constructor anisotropic-tov-conservation-boundary
  field
    conservationEquationEncoded : Bool
    constantBoundaryPressureNeedsPhiPrimeMinusTwo : Bool
    currentWeakFieldDerivativeSatisfiesThatRequirement : Bool
    currentTwoZoneFixtureIsConservationClosed : Bool
    radialPressureProfileMustBeSolvedOrSurfaceLayerAdded : Bool
    fullEinsteinTOVSolveStillRequiredForNonlinearDeviceMetric : Bool

canonicalAnisotropicTOVConservationBoundary :
  AnisotropicTOVConservationBoundary
canonicalAnisotropicTOVConservationBoundary =
  anisotropic-tov-conservation-boundary
    true true false false true true
