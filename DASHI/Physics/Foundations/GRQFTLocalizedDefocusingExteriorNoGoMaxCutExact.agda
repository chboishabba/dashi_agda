{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTLocalizedDefocusingExteriorNoGoMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import Data.Integer.Base as Int
open import Data.Rational.Base using (_/_)

import DASHI.Physics.Foundations.GRQFTFiniteDefocusingSolutionWitnessExact as Defocus
import DASHI.Physics.Foundations.GRQFTFiniteComovingRiemannDeviationExact as Riemann
import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVSystemExact as TOV
import DASHI.Physics.Foundations.GRQFTFiniteRationalTOVExteriorMassCollisionExact as Collision
import DASHI.Physics.Foundations.GRQFTPositiveDensityExteriorRepulsionNoGoExact as NoGo

------------------------------------------------------------------------
-- AUTHORITATIVE LOCALIZED MAX-CUT AFTER LITERAL TOV EXECUTION
--
-- Strongest simultaneous result currently justified:
--
--   * positive-G tension source gives local timelike defocusing;
--   * principal comoving geodesic-deviation directions are outward;
--   * a literal rational anisotropic TOV shell can satisfy radial balance,
--     p_r(R)=0, r>2m at sampled nodes, and negative pressure-weighted active
--     diagnostic;
--   * nevertheless m(R)=+1/4, so the standard vacuum exterior remains on the
--     positive-mass / attractive branch.
--
-- Therefore local defocusing does not compile to standard asymptotically-flat
-- exterior antigravity under the positive-density static spherical assumptions.
------------------------------------------------------------------------

record LocalizedDefocusingExteriorNoGoMaxCut : Set where
  constructor localized-defocusing-exterior-no-go-max-cut
  field
    finiteDefocusing :
      Defocus.FiniteDefocusingSolutionWitness

    comovingRiemannDeviation :
      Riemann.FiniteComovingRiemannDeviationWitness

    literalFiniteTOV :
      TOV.FiniteRationalTOVRepulsiveWitness

    localPrincipalDeviationOutward :
      (i : Riemann.SpatialAxis3) →
      Riemann.principalDeviationAcceleration i
        ≡ Riemann.outwardSeparationAcceleration

    pressureWeightedActiveDiagnosticNegative :
      TOV.finiteIntegratedActiveMass
        ≡ - (Int.+ 11 / 12)

    surfaceMetricMassPositive :
      Collision.surfaceMetricMass
        ≡ Int.+ 1 / 4

    twoMassNotionsDistinct :
      Collision.surfaceMetricMass
        ≡ Collision.pressureWeightedActiveDiagnostic → ⊥

    standardVacuumExteriorAttractive :
      Collision.finiteTOVStandardVacuumExteriorOrientation
        ≡ Collision.positiveMassAttractiveExterior

open LocalizedDefocusingExteriorNoGoMaxCut public

canonicalLocalizedDefocusingExteriorNoGoMaxCut :
  LocalizedDefocusingExteriorNoGoMaxCut
canonicalLocalizedDefocusingExteriorNoGoMaxCut =
  localized-defocusing-exterior-no-go-max-cut
    Defocus.canonicalFiniteDefocusingSolutionWitness
    Riemann.canonicalFiniteComovingRiemannDeviationWitness
    TOV.canonicalFiniteRationalTOVRepulsiveWitness
    Riemann.allPrincipalComovingDeviationDirectionsOutward
    TOV.finiteIntegratedActiveMassIsNegativeElevenTwelfths
    Collision.surfaceMetricMassIsPositiveQuarter
    Collision.surfaceMetricMassIsNotPressureWeightedActiveDiagnostic
    Collision.finiteTOVStandardVacuumExteriorIsAttractive

------------------------------------------------------------------------
-- ROUTE STATUS
------------------------------------------------------------------------

record LocalizedDefocusingExteriorNoGoBoundary : Set where
  constructor localized-defocusing-exterior-no-go-boundary
  field
    positiveGInteriorDefocusingConstructed : Bool
    outwardPrincipalTidalDeviationConstructed : Bool
    literalFiniteTOVBalanceConstructed : Bool
    sampledNoHorizonConditionConstructed : Bool
    pressureWeightedActiveDiagnosticNegative : Bool
    surfaceMetricMassPositive : Bool
    standardVacuumExteriorRepulsionConstructed : Bool
    standardVacuumExteriorAttractionForFixture : Bool
    externalAntigravityNeedsEscapeRoute : Bool

canonicalLocalizedDefocusingExteriorNoGoBoundary :
  LocalizedDefocusingExteriorNoGoBoundary
canonicalLocalizedDefocusingExteriorNoGoBoundary =
  localized-defocusing-exterior-no-go-boundary
    true true true true true true false true true
