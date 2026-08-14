module DASHI.Biology.Physical.PhysicalBiologyDimensionAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / EXISTING OWNER
--
-- Edgar Buckingham,
-- "On Physically Similar Systems; Illustrations of the Use of Dimensional
-- Equations", Physical Review 4 (1914), 345-376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- This module reuses DASHI.Physics.Units.MechanicalDimensionExact rather than
-- rebuilding M-L-T dimensional algebra inside biology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical

-- Diffusion coefficients and kinematic viscosity carry the same M-L-T
-- dimension L^2 T^-1.  This does not identify their constitutive mechanisms.
biologicalDiffusivityMechanicalDimension : Mechanical.MechanicalDimension
biologicalDiffusivityMechanicalDimension =
  Mechanical.kinematicViscosityDimension

diffusivityHasLengthSquaredPerTimeDimension :
  biologicalDiffusivityMechanicalDimension
    ≡ Mechanical._⊗ᴰ_ Mechanical.lengthDimension Mechanical.velocityDimension
diffusivityHasLengthSquaredPerTimeDimension =
  sym Mechanical.viscosityMatchesLengthVelocity

-- Force density has the same M-L-T dimension as a pressure gradient.
biologicalForceDensityMechanicalDimension : Mechanical.MechanicalDimension
biologicalForceDensityMechanicalDimension =
  Mechanical._⊗ᴰ_ Mechanical.pressureDimension Mechanical.inverseLengthDimension

-- Existing continuum dimensional theorem reused literally:
--   pressure gradient = mass density * acceleration.
forceDensityMatchesDensityAcceleration :
  biologicalForceDensityMechanicalDimension
    ≡ Mechanical._⊗ᴰ_
        Mechanical.massDensityDimension Mechanical.accelerationDimension
forceDensityMatchesDensityAcceleration =
  Mechanical.pressureGradientMatchesDensityAcceleration

-- A velocity time derivative has acceleration dimension, so the inertial term
-- rho * dv/dt matches the same force-density carrier.
inertialForceDensityMatchesPressureGradient :
  Mechanical._⊗ᴰ_
    Mechanical.massDensityDimension
    (Mechanical._⊗ᴰ_ Mechanical.velocityDimension Mechanical.frequencyDimension)
  ≡ biologicalForceDensityMechanicalDimension
inertialForceDensityMatchesPressureGradient
  rewrite Mechanical.velocityTimeDerivativeIsAcceleration =
  sym Mechanical.pressureGradientMatchesDensityAcceleration

-- Advection v·grad(v) has acceleration dimension as well.
advectiveForceDensityMatchesPressureGradient :
  Mechanical._⊗ᴰ_
    Mechanical.massDensityDimension
    (Mechanical._⊗ᴰ_ Mechanical.velocityDimension Mechanical.velocityGradientDimension)
  ≡ biologicalForceDensityMechanicalDimension
advectiveForceDensityMatchesPressureGradient
  rewrite Mechanical.advectionIsAcceleration =
  sym Mechanical.pressureGradientMatchesDensityAcceleration

------------------------------------------------------------------------
-- Boundary: equality of dimensions licenses addition/comparison only at the
-- dimensional level.  Constitutive coefficients, biological material regime,
-- and solution theory remain separate obligations.
------------------------------------------------------------------------
