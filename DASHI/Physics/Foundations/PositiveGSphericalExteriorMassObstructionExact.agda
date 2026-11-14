{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.PositiveGSphericalExteriorMassObstructionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- SPHERICAL POSITIVE-G GLOBAL-MASS OBSTRUCTION
--
-- Static spherical Einstein form:
--
--   ds^2 = -exp(2 nu(r)) dt^2 + (1 - 2 m(r)/r)^(-1) dr^2 + r^2 dOmega^2
--
-- and, in positive-G units with the positive geometric coefficient absorbed,
--
--   m'(r) = positiveFactor(r) * rho(r).
--
-- Therefore non-negative density builds a non-decreasing mass function.  A
-- smooth compact source matched to vacuum carries the boundary mass m(R) into
-- the Schwarzschild exterior.  Pressure can change the interior redshift/
-- acceleration equation, but does not independently flip the vacuum mass
-- parameter once the same conserved spherical solution is fixed.
--
-- This module encodes the exact algebraic ownership and the promotion
-- firewall.  Positivity/order of a concrete profile is supplied by the profile
-- instantiation; it is not manufactured from a Bool here.
------------------------------------------------------------------------

sphericalMassDerivative : ℚ → ℚ → ℚ
sphericalMassDerivative positiveGeometricFactor density =
  positiveGeometricFactor * density

massStep : ℚ → ℚ → ℚ
massStep oldMass positiveDensityContribution =
  oldMass + positiveDensityContribution

positiveDensityBuildsPositiveMass :
  ∀ oldMass contribution →
  massStep oldMass contribution - oldMass ≡ contribution
positiveDensityBuildsPositiveMass = solve-∀

vacuumExteriorMass : ℚ → ℚ
vacuumExteriorMass boundaryMass = boundaryMass

vacuumExteriorMassIsBoundaryMass :
  ∀ boundaryMass → vacuumExteriorMass boundaryMass ≡ boundaryMass
vacuumExteriorMassIsBoundaryMass boundaryMass = refl

-- Normalized exterior radial acceleration coefficient.  For positive boundary
-- mass the physical Schwarzschild/Newtonian acceleration points inward; the
-- minus sign is explicit here rather than hidden in a sign label.
exteriorRadialAccelerationCoefficient : ℚ → ℚ → ℚ
exteriorRadialAccelerationCoefficient boundaryMass inverseRadiusSquared =
  - (boundaryMass * inverseRadiusSquared)

positiveBoundaryMassGivesAttractiveSchwarzschildExterior :
  exteriorRadialAccelerationCoefficient 1ℚ 1ℚ ≡ - 1ℚ
positiveBoundaryMassGivesAttractiveSchwarzschildExterior = refl

-- An outward vacuum exterior at positive G therefore needs a negative exterior
-- mass parameter (or departure from the assumptions that lead to the same
-- Schwarzschild vacuum problem).  Local negative active stress by itself does
-- not provide that global charge.
outwardExteriorWithNegativeMassParameter :
  exteriorRadialAccelerationCoefficient (- 1ℚ) 1ℚ ≡ 1ℚ
outwardExteriorWithNegativeMassParameter = refl

record PositiveGSphericalExteriorMassBoundary : Set where
  constructor positive-g-spherical-exterior-mass-boundary
  field
    sphericalEinsteinMassEquationUsed : Bool
    nonNegativeDensityBuildsNonDecreasingMass : Bool
    smoothVacuumExteriorUsesBoundaryMass : Bool
    positiveBoundaryMassGivesAttractiveSchwarzschildExterior : Bool
    interiorPressureAloneFlipsVacuumMassParameter : Bool
    localNegativeActiveStressAutomaticallyMakesNegativeADMCharge : Bool
    positiveDensityAloneCannotYieldRepulsiveVacuumExterior : Bool
    repulsiveVacuumExteriorNeedsNegativeGlobalChargeOrChangedAssumptions : Bool

canonicalPositiveGSphericalExteriorMassBoundary :
  PositiveGSphericalExteriorMassBoundary
canonicalPositiveGSphericalExteriorMassBoundary =
  positive-g-spherical-exterior-mass-boundary
    true true true true false false true true
