module DASHI.Cognition.ModeGeometrySurface where

------------------------------------------------------------------------
-- Generic pattern surface.
--
-- This file records the common DASHI shape behind several pattern
-- generators:
--   * Turing / reaction-diffusion patterning,
--   * modular or lattice harmonic summation,
--   * endogenous visual / Klüver-form projection.
--
-- The object is intentionally weak.  It says that a carrier, a mode
-- spectrum, and a projection geometry can produce an observed geometry.
-- It does not identify the observation with semantic content and it does
-- not permit reverse recovery of the hidden carrier state.

record ModeGeometrySurface : Set₁ where
  constructor modeGeometrySurface
  field
    Carrier : Set
    Symmetry : Set
    ModeSpectrum : Set
    SelectionLaw : ModeSpectrum → Set
    ProjectionGeometry : Set
    ObservedGeometry : Set

    selectedModesStabiliseGeometry : Set
    observedGeometryIsProjected : Set

    noCarrierRecovery : Set
    noSemanticAuthority : Set

------------------------------------------------------------------------
-- Explicit anti-promotion boundary.

record ObservableContactGeometryBoundary : Set₁ where
  constructor observableContactGeometryBoundary
  field
    surface : ModeGeometrySurface

    contactIsReal : Set
    contactIsLossyProjection : Set

    notHiddenTruth : Set
    notClinicalDiagnosis : Set
    notMysticalAuthority : Set
    notCulturalUniversalityTheorem : Set

------------------------------------------------------------------------
-- Tags for the three motivating lanes.  These are tags only, not proof
-- promotions.

data ModeGeometryLane : Set where
  turingReactionDiffusionLane : ModeGeometryLane
  klueverVisualProjectionLane : ModeGeometryLane
  eisensteinSymmetrySummationLane : ModeGeometryLane

record LaneStampedModeGeometry : Set₁ where
  constructor laneStampedModeGeometry
  field
    lane : ModeGeometryLane
    surface : ModeGeometrySurface
    boundary : ObservableContactGeometryBoundary
