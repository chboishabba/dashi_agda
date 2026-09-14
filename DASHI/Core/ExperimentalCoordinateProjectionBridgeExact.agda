module DASHI.Core.ExperimentalCoordinateProjectionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.CoarseFineFabricCalculusExact as Calculus

------------------------------------------------------------------------
-- EXPERIMENTAL COORDINATE SEPARATION -> PROJECTION COLLISION
--
-- A coordinate that separates two worlds already collapsed by the current
-- observer is exactly a projection-collision witness for the coordinate readout.
------------------------------------------------------------------------

coordinateSeparationYieldsProjectionCollision :
  ∀ {World Control Value Dimension ExistingCode : Set}
    {design : Coordinate.ExperimentalCoordinateDesign
      World Control Value Dimension}
    {existing : World → ExistingCode} →
  Coordinate.CoordinateSeparatesCollision design existing →
  Calculus.ProjectionCollision
    existing
    (λ world →
      Coordinate.read design
        (Coordinate.coordinate
          (let open Coordinate.CoordinateSeparatesCollision in
           ?))
        world)
coordinateSeparationYieldsProjectionCollision = ?
