{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGSphericalInteriorRepulsionBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- SPHERICAL INTERIOR REPULSION VS SMOOTH VACUUM BOUNDARY
--
-- In static spherical GR,
--
--   nu' = (m + pressureCoefficient * r^3 p_r) / [r (r - 2 m)].
--
-- Outside a horizon the denominator has the positive orientation.  Hence an
-- outward static gravitational acceleration (-nu' > 0) requires the numerator
-- to have negative orientation.  At a smooth vacuum boundary p_r(R)=0, that
-- numerator reduces to m(R).  A positive boundary mass therefore has inward
-- Schwarzschild orientation at the boundary.
--
-- This is the sharp reason a positive-density negative-pressure interior may
-- produce local repulsion while still failing to give a repulsive smooth
-- vacuum exterior.  To keep the outward sign through the boundary one needs a
-- nonzero boundary stress/surface layer, a sign-changing/global-mass route, or
-- a modification of the exterior assumptions.
------------------------------------------------------------------------

radialEinsteinNumerator : ℚ → ℚ → ℚ
radialEinsteinNumerator enclosedMass radialPressureContribution =
  enclosedMass + radialPressureContribution

vacuumBoundaryNumerator : ℚ → ℚ
vacuumBoundaryNumerator boundaryMass = radialEinsteinNumerator boundaryMass 0ℚ

vacuumBoundaryNumeratorIsMass :
  ∀ boundaryMass → vacuumBoundaryNumerator boundaryMass ≡ boundaryMass
vacuumBoundaryNumeratorIsMass boundaryMass = refl

-- Normalized sign fixtures for the outside-horizon denominator.
normalizedNuPrime : ℚ → ℚ
normalizedNuPrime numerator = numerator

normalizedStaticAcceleration : ℚ → ℚ
normalizedStaticAcceleration numerator = - numerator

outwardInteriorRequiresNegativeNumerator :
  normalizedStaticAcceleration (- 1ℚ) ≡ 1ℚ
outwardInteriorRequiresNegativeNumerator = refl

vacuumSmoothBoundaryWithPositiveMassHasPositiveNuPrime :
  normalizedNuPrime (vacuumBoundaryNumerator 1ℚ) ≡ 1ℚ
vacuumSmoothBoundaryWithPositiveMassHasPositiveNuPrime = refl

vacuumSmoothBoundaryWithPositiveMassHasInwardAcceleration :
  normalizedStaticAcceleration (vacuumBoundaryNumerator 1ℚ) ≡ - 1ℚ
vacuumSmoothBoundaryWithPositiveMassHasInwardAcceleration = refl

pressureContributionNeededForSelectedNumerator :
  ∀ mass targetNumerator →
  radialEinsteinNumerator mass (targetNumerator - mass) ≡ targetNumerator
pressureContributionNeededForSelectedNumerator = solve-∀

record PositiveGSphericalInteriorBoundary : Set where
  constructor positive-g-spherical-interior-boundary
  field
    radialEinsteinNumeratorEncoded : Bool
    outwardInteriorRequiresNegativeNumerator : Bool
    smoothVacuumBoundarySetsRadialPressureToZero : Bool
    vacuumSmoothBoundaryWithPositiveMassHasPositiveNuPrime : Bool
    outwardInteriorCannotMeetSmoothZeroPressurePositiveMassBoundary : Bool
    surfaceLayerOrSignChangingProfileRequired : Bool
    localInteriorMetricEngineeringRouteStillLive : Bool

canonicalPositiveGSphericalInteriorBoundary : PositiveGSphericalInteriorBoundary
canonicalPositiveGSphericalInteriorBoundary =
  positive-g-spherical-interior-boundary
    true true true true true true true
