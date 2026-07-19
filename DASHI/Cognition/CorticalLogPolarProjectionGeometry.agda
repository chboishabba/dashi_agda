module DASHI.Cognition.CorticalLogPolarProjectionGeometry where

------------------------------------------------------------------------
-- Qualitative retinotopic / log-polar projection geometry.
--
-- This module formalises the geometry layer between a selected carrier mode
-- and a coarse Klüver form class.  It does not assert a complete empirical
-- model of retina or cortex.

open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverForm
  ; latticeGrating
  ; tunnelFunnel
  ; spiral
  ; radialCobweb
  )

------------------------------------------------------------------------
-- Mode-coordinate features used by the coarse projection relation.

data VisualModeFeature : Set where
  translationalPeriodicity : VisualModeFeature
  angularPeriodicity : VisualModeFeature
  radialPeriodicity : VisualModeFeature
  angularPhaseDrift : VisualModeFeature
  radialPhaseDrift : VisualModeFeature
  orientationPinwheelBias : VisualModeFeature
  logRadiusTranslation : VisualModeFeature

record CorticalProjectionGeometry : Set₁ where
  constructor corticalProjectionGeometry
  field
    RetinalCoordinate : Set
    CorticalCoordinate : Set
    Mode : Set

    retinotopicMap : RetinalCoordinate → CorticalCoordinate
    logPolarChart : RetinalCoordinate → CorticalCoordinate
    feature : Mode → VisualModeFeature

    orientationSensitive : Set
    locallyCoupled : Set
    projectionIsLossy : Set

------------------------------------------------------------------------
-- Coarse, non-exclusive projection hints.

data FeatureProjectsAs : VisualModeFeature → KlueverForm → Set where
  translationAsLattice :
    FeatureProjectsAs translationalPeriodicity latticeGrating
  logRadiusAsTunnel :
    FeatureProjectsAs logRadiusTranslation tunnelFunnel
  angularDriftAsSpiral :
    FeatureProjectsAs angularPhaseDrift spiral
  radialPeriodAsCobweb :
    FeatureProjectsAs radialPeriodicity radialCobweb
  angularPeriodAsCobweb :
    FeatureProjectsAs angularPeriodicity radialCobweb
  radialDriftAsTunnel :
    FeatureProjectsAs radialPhaseDrift tunnelFunnel

record CorticalModeProjection : Set₁ where
  constructor corticalModeProjection
  field
    geometry : CorticalProjectionGeometry
    selectedMode : CorticalProjectionGeometry.Mode geometry
    observedForm : KlueverForm

    projectionWitness :
      FeatureProjectsAs
        (CorticalProjectionGeometry.feature geometry selectedMode)
        observedForm

    noUniqueInverseMode : Set
    noUniqueInverseCarrier : Set
    noSemanticAuthority : Set
