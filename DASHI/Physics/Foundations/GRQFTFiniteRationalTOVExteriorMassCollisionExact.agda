{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTFiniteRationalTOVExteriorMassCollisionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; _/_; _<_; _≤_)

import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local

------------------------------------------------------------------------
-- EXTERIOR MASS COLLISION
--
-- The literal finite TOV construction gives two distinct quantities:
--
--   m(R) = +1/4                    (metric / Misner-Sharp-style mass function)
--   integral(rho+p_r+2p_t) = -11/12  (pressure-weighted active-stress diagnostic)
--
-- A standard vacuum Schwarzschild exterior is controlled by m(R), not by
-- silently replacing it with the pressure-weighted diagnostic.
--
-- Therefore the earlier generic "negative active mass -> outward exterior"
-- adapter is NOT licensed for this literal TOV fixture without an additional
-- theorem identifying the exterior mass parameter with that active diagnostic.
------------------------------------------------------------------------

surfaceMetricMass : ℚ
surfaceMetricMass = TOV.outerMassTarget

surfaceMetricMassIsPositiveQuarter :
  surfaceMetricMass ≡ Int.+ 1 / 4
surfaceMetricMassIsPositiveQuarter = refl

pressureWeightedActiveDiagnostic : ℚ
pressureWeightedActiveDiagnostic = TOV.finiteIntegratedActiveMass

pressureWeightedActiveDiagnosticIsNegativeElevenTwelfths :
  pressureWeightedActiveDiagnostic ≡ - (Int.+ 11 / 12)
pressureWeightedActiveDiagnosticIsNegativeElevenTwelfths =
  TOV.finiteIntegratedActiveMassIsNegativeElevenTwelfths

surfaceMetricMassIsNotPressureWeightedActiveDiagnostic :
  surfaceMetricMass ≡ pressureWeightedActiveDiagnostic → ⊥
surfaceMetricMassIsNotPressureWeightedActiveDiagnostic ()

data StandardVacuumExteriorOrientation : Set where
  positiveMassAttractiveExterior : StandardVacuumExteriorOrientation
  zeroMassFlatExterior : StandardVacuumExteriorOrientation
  negativeMassRepulsiveExterior : StandardVacuumExteriorOrientation

-- Specialized exact fixture statement.  We deliberately avoid pretending a
-- generic ordered-rational exterior classifier has been implemented here.
finiteTOVStandardVacuumExteriorOrientation :
  StandardVacuumExteriorOrientation
finiteTOVStandardVacuumExteriorOrientation =
  positiveMassAttractiveExterior

finiteTOVStandardVacuumExteriorIsAttractive :
  finiteTOVStandardVacuumExteriorOrientation
    ≡ positiveMassAttractiveExterior
finiteTOVStandardVacuumExteriorIsAttractive = refl

------------------------------------------------------------------------
-- CONSEQUENCE FOR THE PREVIOUS LOCALIZED ADAPTER
------------------------------------------------------------------------

data ExteriorRepulsionClosureStatus : Set where
  activeStressDiagnosticOnly : ExteriorRepulsionClosureStatus
  exteriorMetricRepulsionProved : ExteriorRepulsionClosureStatus
  standardVacuumExteriorAttractive : ExteriorRepulsionClosureStatus

finiteTOVExteriorClosureStatus :
  ExteriorRepulsionClosureStatus
finiteTOVExteriorClosureStatus =
  standardVacuumExteriorAttractive

record ExteriorMassCollisionBoundary : Set where
  constructor exterior-mass-collision-boundary
  field
    surfaceMetricMassPositive : Bool
    pressureWeightedActiveDiagnosticNegative : Bool
    twoMassNotionsEqualInFixture : Bool
    negativeActiveDiagnosticAloneProvesExteriorRepulsion : Bool
    standardVacuumExteriorAttractiveForFixture : Bool
    nonstandardJunctionOrExteriorLawNeededForRepulsion : Bool
    earlierActiveMassAdapterMayBeUsedAsDiagnosticOnly : Bool

canonicalExteriorMassCollisionBoundary :
  ExteriorMassCollisionBoundary
canonicalExteriorMassCollisionBoundary =
  exterior-mass-collision-boundary
    true true false false true true true
