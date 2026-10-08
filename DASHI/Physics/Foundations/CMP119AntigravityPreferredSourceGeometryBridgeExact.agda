{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPreferredSourceGeometryBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)

import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as CMP119
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4
import DASHI.Physics.Foundations.CMP119AntigravitySelectedVacuumProjectorExact as Vacuum
import DASHI.Physics.Foundations.CMP119AntigravitySelectedMetricFamilyTraceClosureExact as Trace
import DASHI.Physics.Foundations.GRQFTKottlerRepulsionParameterWindowExact as Window

------------------------------------------------------------------------
-- PREFERRED SOURCE -> GEOMETRY BRIDGE
--
-- Two older synthetic leaves are avoidable on the preferred route:
--
--   * no independent Vacuum -> Q readout: the selected source already uses
--     LocalizedAction and its existing plaquetteCoefficientProjector;
--   * no constructorless old pinned-stress ancestry authority: the preferred
--     metric-family source capstone already proves strict negativity of the
--     selected diagonal active sum on the actual selected CMP119 stress lane
--     through SelectedMetricFamilySU2ClosureInput and
--     selectedMetricFamilyDiagonalActiveSumNegative.
--
-- Geometry should therefore consume the amplitudes the source ACTUALLY
-- produces.  We do not require those amplitudes to equal the historical
-- 21/64,19/48 rational fixture.
------------------------------------------------------------------------

module _
  {Density Background Fluctuation : Set}
  (source : CMP119.CMP119Section2SourceNativeState
    Density Background Fluctuation
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction
    T4.LocalizedAction T4.LocalizedAction T4.LocalizedAction)
  where

  sourceVacuumAmplitude : Nat → ℚ
  sourceVacuumAmplitude = Vacuum.selectedVacuumAmplitude source

  -- Kottler's exact parameter-window owner uses L = Lambda R^3.
  sourceScaledLambda : Nat → ℚ → ℚ
  sourceScaledLambda scale radius =
    sourceVacuumAmplitude scale * radius * radius * radius

  sourceOutwardMargin : Nat → ℚ → ℚ → ℚ
  sourceOutwardMargin scale mass radius =
    Window.outwardAccelerationMargin
      mass (sourceScaledLambda scale radius)

  sourceStaticPatchMargin : Nat → ℚ → ℚ → ℚ
  sourceStaticPatchMargin scale mass radius =
    Window.staticPatchMargin
      mass radius (sourceScaledLambda scale radius)

  record SourceSelectedKottlerWindow
      (scale : Nat) (mass radius : ℚ) : Set where
    constructor source-selected-kottler-window
    field
      outwardMarginPositive :
        0ℚ < sourceOutwardMargin scale mass radius
      staticPatchMarginPositive :
        0ℚ < sourceStaticPatchMargin scale mass radius

  open SourceSelectedKottlerWindow public

  -- This is the honest remaining source-to-geometry obligation: find/bound a
  -- literal source scale whose already-owned vacuum projector lies in the
  -- exact Kottler window.  It replaces equality to one hand-picked fixture.
  record SourceSelectedTwoRegionGeometry
      (interiorScale exteriorScale : Nat)
      (mass radius : ℚ) : Set where
    constructor source-selected-two-region-geometry
    field
      exteriorWindow :
        SourceSelectedKottlerWindow exteriorScale mass radius
      interiorAmplitude : ℚ
      exteriorAmplitude : ℚ
      interiorAmplitudeIsSource :
        interiorAmplitude ≡ sourceVacuumAmplitude interiorScale
      exteriorAmplitudeIsSource :
        exteriorAmplitude ≡ sourceVacuumAmplitude exteriorScale

record PreferredSourceGeometryBridgeBoundary : Set where
  constructor preferred-source-geometry-bridge-boundary
  field
    literalEq223VacuumProjectorAvailable : Bool
    geometryParameterizedByActualSourceAmplitude : Bool
    historicalMagicAmplitudeEqualityRequired : Bool
    preferredSelectedSourceStressSameObjectRouteAvailable : Bool
    oldConstructorlessPinnedStressAuthorityRequired : Bool
    independentAbstractVacuumReadoutStillRequired : Bool
    selectedMetricFamilyTraceClosureOwnerReused : Bool
    sourceScaleWindowMembershipStillNeedsProof : Bool
    SIAmplitudeCalibrationStillNeedsProof : Bool

canonicalPreferredSourceGeometryBridgeBoundary :
  PreferredSourceGeometryBridgeBoundary
canonicalPreferredSourceGeometryBridgeBoundary =
  preferred-source-geometry-bridge-boundary
    true true false true false false true true true

-- Keep the exact preferred owner visible at this bridge.  Its theorem is
-- `Trace.selectedMetricFamilyDiagonalActiveSumNegative` and its input carrier
-- is `Trace.SelectedMetricFamilySU2ClosureInput`; no replacement stress
-- equality is introduced here.
preferredTraceOwnerPresent : Bool
preferredTraceOwnerPresent = true
