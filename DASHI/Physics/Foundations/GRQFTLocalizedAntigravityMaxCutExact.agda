{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTLocalizedAntigravityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.Foundations.GRQFTFiniteDefocusingSolutionWitnessExact as Defocus
import DASHI.Physics.Foundations.GRQFTFiniteComovingRiemannDeviationExact as Riemann
import DASHI.Physics.Foundations.GRQFTLocalizedRepulsiveSourceCriterionExact as Local

------------------------------------------------------------------------
-- LOCALIZED ANTIGRAVITY MAX-CUT
--
-- This packages the strongest same-object conclusion presently available from
-- the GRQFT finite fixture plus the explicit localized weak-field adapter.
--
-- It simultaneously retains:
--
--   * positive normalized gravitational coupling;
--   * negative pressure/tension active source;
--   * negative timelike Ricci / positive Raychaudhuri defocusing;
--   * outward principal comoving geodesic-deviation directions;
--   * outward external-test-mass response under the declared localized
--     stationary/weak-field/spherical active-mass adapter.
--
-- No negative G or negative inertial mass is used.
------------------------------------------------------------------------

record LocalizedPositiveGAntigravityMaxCut : Set where
  constructor localized-positive-g-antigravity-max-cut
  field
    finiteDefocusing :
      Defocus.FiniteDefocusingSolutionWitness

    comovingRiemannDeviation :
      Riemann.FiniteComovingRiemannDeviationWitness

    localizedExteriorCriterion :
      Local.LocalizedPositiveGRepulsiveSourceWitness

    couplingSign : Signed.CouplingSign
    couplingIsPositive :
      couplingSign ≡ Signed.positiveCoupling

    xPrincipalDeviationOutward :
      Riemann.principalDeviationAcceleration Riemann.xSpatial
        ≡ Riemann.outwardSeparationAcceleration

    yPrincipalDeviationOutward :
      Riemann.principalDeviationAcceleration Riemann.ySpatial
        ≡ Riemann.outwardSeparationAcceleration

    zPrincipalDeviationOutward :
      Riemann.principalDeviationAcceleration Riemann.zSpatial
        ≡ Riemann.outwardSeparationAcceleration

    externalTestMassResponse :
      Local.ExteriorRadialResponse
    externalTestMassResponseIsOutward :
      externalTestMassResponse ≡ Local.outwardExteriorAcceleration

open LocalizedPositiveGAntigravityMaxCut public

canonicalLocalizedPositiveGAntigravityMaxCut :
  LocalizedPositiveGAntigravityMaxCut
canonicalLocalizedPositiveGAntigravityMaxCut =
  localized-positive-g-antigravity-max-cut
    Defocus.canonicalFiniteDefocusingSolutionWitness
    Riemann.canonicalFiniteComovingRiemannDeviationWitness
    Local.canonicalLocalizedPositiveGRepulsiveSourceWitness
    Signed.positiveCoupling
    refl
    Riemann.xDeviationIsOutward
    Riemann.yDeviationIsOutward
    Riemann.zDeviationIsOutward
    Local.outwardExteriorAcceleration
    refl

------------------------------------------------------------------------
-- Strongest theorem-shaped projections.
------------------------------------------------------------------------

localizedPositiveGExternalRepulsion :
  externalTestMassResponse canonicalLocalizedPositiveGAntigravityMaxCut
    ≡ Local.outwardExteriorAcceleration
localizedPositiveGExternalRepulsion = refl

localizedPositiveGAllPrincipalTidalDirectionsOutward :
  (i : Riemann.SpatialAxis3) →
  Riemann.principalDeviationAcceleration i
    ≡ Riemann.outwardSeparationAcceleration
localizedPositiveGAllPrincipalTidalDirectionsOutward =
  Riemann.allPrincipalComovingDeviationDirectionsOutward

localizedAntigravityDoesNotRequireNegativeG :
  couplingSign canonicalLocalizedPositiveGAntigravityMaxCut
    ≡ Signed.positiveCoupling
localizedAntigravityDoesNotRequireNegativeG = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LocalizedAntigravityMaxCutBoundary : Set where
  constructor localized-antigravity-max-cut-boundary
  field
    positiveGCouplingRetained : Bool
    negativePressureTensionMechanismRetained : Bool
    timelikeDefocusingRetained : Bool
    indexedPrincipalGeodesicDeviationOutward : Bool
    externalTestMassRepulsionCriterionRetained : Bool
    negativeGRequired : Bool
    negativeInertialMassRequired : Bool
    arbitraryStaticMetricSolved : Bool
    fullTolmanKomarDerivationInternal : Bool
    continuumMagnitudeCalibrated : Bool

canonicalLocalizedAntigravityMaxCutBoundary :
  LocalizedAntigravityMaxCutBoundary
canonicalLocalizedAntigravityMaxCutBoundary =
  localized-antigravity-max-cut-boundary
    true true true true true false false false false false
