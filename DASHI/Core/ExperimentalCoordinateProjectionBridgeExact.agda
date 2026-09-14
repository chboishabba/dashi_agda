module DASHI.Core.ExperimentalCoordinateProjectionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join

------------------------------------------------------------------------
-- EXPERIMENTAL COORDINATE SEPARATION -> PROJECTION COLLISION
--
-- A coordinate that separates two worlds already collapsed by the current
-- observer is exactly a projection-collision witness for that coordinate's
-- readout.  No new physical dimension, authority, or dynamics is created.
------------------------------------------------------------------------

coordinateSeparationYieldsProjectionCollision :
  ∀ {World Control Value Dimension ExistingCode : Set}
    {design : Coordinate.ExperimentalCoordinateDesign
      World Control Value Dimension}
    {existing : World → ExistingCode} →
  (separation : Coordinate.CoordinateSeparatesCollision design existing) →
  Calculus.ProjectionCollision
    existing
    (Coordinate.read design (Coordinate.coordinate separation))
coordinateSeparationYieldsProjectionCollision separation =
  Calculus.projectionCollision
    (Coordinate.left separation)
    (Coordinate.right separation)
    (Coordinate.currentlyCollapsed separation)
    (Coordinate.coordinateSeparates separation)

coordinateReadCannotFactorThroughExisting :
  ∀ {World Control Value Dimension ExistingCode : Set}
    {design : Coordinate.ExperimentalCoordinateDesign
      World Control Value Dimension}
    {existing : World → ExistingCode} →
  (separation : Coordinate.CoordinateSeparatesCollision design existing) →
  (coarseRead : ExistingCode → Value) →
  ((world : World) →
    Coordinate.read design (Coordinate.coordinate separation) world
    ≡ coarseRead (existing world)) →
  ⊥
coordinateReadCannotFactorThroughExisting separation =
  Calculus.consumerCannotFactorThroughProjection
    (coordinateSeparationYieldsProjectionCollision separation)

------------------------------------------------------------------------
-- Constructive observer repair.
--
-- Once the missing coordinate is identified, the least-inventive refinement is
-- the product observer retaining both the old surface and the new coordinate.
-- RequiredObserverAxisJoinAdequacyExact already owns the product law; this
-- bridge merely instantiates it at the coordinate discovered by the collision.
------------------------------------------------------------------------

coordinateJoinRetainsExistingAndNewAxis :
  ∀ {World Control Value Dimension ExistingCode : Set}
    {design : Coordinate.ExperimentalCoordinateDesign
      World Control Value Dimension}
    {existing : World → ExistingCode} →
  (separation : Coordinate.CoordinateSeparatesCollision design existing) →
  Join.RetainsBothRequiredAxes
    (Join.jointAxis
      existing
      (Coordinate.read design (Coordinate.coordinate separation)))
    existing
    (Coordinate.read design (Coordinate.coordinate separation))
coordinateJoinRetainsExistingAndNewAxis
  {design = design} {existing = existing} separation =
  Join.retainsBothRequiredAxes
    (Join.jointRetainsLeft
      existing
      (Coordinate.read design (Coordinate.coordinate separation)))
    (Join.jointRetainsRight
      existing
      (Coordinate.read design (Coordinate.coordinate separation)))

record ExperimentalCoordinateProjectionBoundary : Set where
  constructor experimental-coordinate-projection-boundary
  field
    coordinateSeparationCreatesProjectionCollision : Bool
    collisionRefutesExistingObserverFactorisation : Bool
    coordinateSeparationCreatesPhysicalDimension : Bool
    coordinateSeparationCreatesDynamicDefect : Bool
    coordinateSeparationCreatesManipulationAuthority : Bool

canonicalExperimentalCoordinateProjectionBoundary :
  ExperimentalCoordinateProjectionBoundary
canonicalExperimentalCoordinateProjectionBoundary =
  experimental-coordinate-projection-boundary
    true
    true
    false
    false
    false
