{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSClayForcedBreakdownSourceCoordinatesExact where

------------------------------------------------------------------------
-- Canonical non-Round source-coordinate owner for Fefferman alternatives C/D.
--
-- Source authority:
--   Charles L. Fefferman,
--   "Existence and Smoothness of the Navier--Stokes Equation",
--   Clay Mathematics Institute Millennium Prize Problem description (2000).
--
-- DASHI extension:
--   This module extracts the constructor-distinct coordinate audit formerly
--   carried by historical Round523.  It preserves the source-facing truth
--   table only; it does not prove either Clay alternative and does not promote
--   any historical Round module to theorem authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- Source coordinates.
------------------------------------------------------------------------

data ClayBreakdownDomain : Set where
  euclideanR3 : ClayBreakdownDomain
  periodicT3 : ClayBreakdownDomain

data ClayBreakdownCoordinate : Set where
  positiveViscosity : ClayBreakdownCoordinate
  dimensionThree : ClayBreakdownCoordinate
  smoothDivergenceFreeInitialDatum : ClayBreakdownCoordinate
  rapidInitialSpatialDecay : ClayBreakdownCoordinate
  periodicInitialDatum : ClayBreakdownCoordinate
  smoothForcing : ClayBreakdownCoordinate
  rapidForcingSpaceTimeDecay : ClayBreakdownCoordinate
  periodicForcing : ClayBreakdownCoordinate
  rapidForcingTimeDecay : ClayBreakdownCoordinate
  exactNavierStokesEquation : ClayBreakdownCoordinate
  noGlobalSmoothSolution : ClayBreakdownCoordinate
  boundedEnergyRequirement : ClayBreakdownCoordinate
  periodicSolutionRequirement : ClayBreakdownCoordinate

data ClayBreakdownAlternative : Set where
  clayAlternativeC : ClayBreakdownAlternative
  clayAlternativeD : ClayBreakdownAlternative

requiredByC : ClayBreakdownCoordinate → Bool
requiredByC positiveViscosity = true
requiredByC dimensionThree = true
requiredByC smoothDivergenceFreeInitialDatum = true
requiredByC rapidInitialSpatialDecay = true
requiredByC periodicInitialDatum = false
requiredByC smoothForcing = true
requiredByC rapidForcingSpaceTimeDecay = true
requiredByC periodicForcing = false
requiredByC rapidForcingTimeDecay = false
requiredByC exactNavierStokesEquation = true
requiredByC noGlobalSmoothSolution = true
requiredByC boundedEnergyRequirement = true
requiredByC periodicSolutionRequirement = false

requiredByD : ClayBreakdownCoordinate → Bool
requiredByD positiveViscosity = true
requiredByD dimensionThree = true
requiredByD smoothDivergenceFreeInitialDatum = true
requiredByD rapidInitialSpatialDecay = false
requiredByD periodicInitialDatum = true
requiredByD smoothForcing = true
requiredByD rapidForcingSpaceTimeDecay = false
requiredByD periodicForcing = true
requiredByD rapidForcingTimeDecay = true
requiredByD exactNavierStokesEquation = true
requiredByD noGlobalSmoothSolution = true
requiredByD boundedEnergyRequirement = false
requiredByD periodicSolutionRequirement = true
