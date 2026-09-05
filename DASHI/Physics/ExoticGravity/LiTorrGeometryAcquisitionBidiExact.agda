module DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrStandardGRRotatingSourceKernelExact as GR

------------------------------------------------------------------------
-- LI/TORR SAME-APPARATUS GEOMETRY ACQUISITION
--
-- The weak-field GR kernel is available.  The missing object is the exact
-- apparatus instance needed to turn the kernel into a literal same-geometry
-- magnitude comparator.
------------------------------------------------------------------------

data GeometryLeaf : Set where
  sourceShapeLeaf : GeometryLeaf
  sourceMassLeaf : GeometryLeaf
  sourceRadiusLeaf : GeometryLeaf
  sourceAngularVelocityLeaf : GeometryLeaf
  coherentMassCurrentLeaf : GeometryLeaf
  driveWaveformLeaf : GeometryLeaf
  probeLocationLeaf : GeometryLeaf
  materialStateLeaf : GeometryLeaf
  closedGeometry : GeometryLeaf

record GeometryClosureState : Set where
  constructor geometry-closure-state
  field
    sourceShapeOwned : Bool
    sourceMassOwned : Bool
    sourceRadiusOwned : Bool
    sourceAngularVelocityOwned : Bool
    coherentMassCurrentOwned : Bool
    driveWaveformOwned : Bool
    probeLocationOwned : Bool
    materialStateOwned : Bool

firstOpenGeometryLeaf : GeometryClosureState → GeometryLeaf
firstOpenGeometryLeaf (geometry-closure-state false m r w j d p s) = sourceShapeLeaf
firstOpenGeometryLeaf (geometry-closure-state true false r w j d p s) = sourceMassLeaf
firstOpenGeometryLeaf (geometry-closure-state true true false w j d p s) = sourceRadiusLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true false j d p s) = sourceAngularVelocityLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true true false d p s) = coherentMassCurrentLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true true true false p s) = driveWaveformLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true true true true false s) = probeLocationLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true true true true true false) = materialStateLeaf
firstOpenGeometryLeaf (geometry-closure-state true true true true true true true true) = closedGeometry

------------------------------------------------------------------------
-- Current source-paper state.
--
-- The historical papers provide mechanism equations and an illustrative
-- coherent volume, but not a unique, fully instantiated source/probe geometry.
-- We therefore keep the first literal apparatus coordinate open.
------------------------------------------------------------------------

currentHistoricalGeometryState : GeometryClosureState
currentHistoricalGeometryState =
  geometry-closure-state false false false false false false false true

currentFirstOpenGeometryLeaf : GeometryLeaf
currentFirstOpenGeometryLeaf = firstOpenGeometryLeaf currentHistoricalGeometryState

record GeometryPromotionBoundary : Set where
  constructor geometry-promotion-boundary
  field
    arbitraryVolumeClosesSourceShape : Bool
    arbitraryVolumeClosesSourceShapeIsFalse :
      arbitraryVolumeClosesSourceShape ≡ false

    genericLaboratoryScaleClosesProbeLocation : Bool
    genericLaboratoryScaleClosesProbeLocationIsFalse :
      genericLaboratoryScaleClosesProbeLocation ≡ false

    standardGRKernelMayPreexistGeometryClosure : Bool
    standardGRKernelMayPreexistGeometryClosureIsTrue :
      standardGRKernelMayPreexistGeometryClosure ≡ true

    literalMagnitudeComparatorRequiresClosedGeometry : Bool
    literalMagnitudeComparatorRequiresClosedGeometryIsTrue :
      literalMagnitudeComparatorRequiresClosedGeometry ≡ true

canonicalGeometryPromotionBoundary : GeometryPromotionBoundary
canonicalGeometryPromotionBoundary =
  geometry-promotion-boundary false refl false refl true refl true refl
