module DASHI.Biology.TwoBoundarySymmetryResolvedModeSectionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TwoBoundaryHyperformalismExact as Two
import DASHI.Biology.ObserverRelativeReachableSubfabricExact as Reach

------------------------------------------------------------------------
-- TWO-BOUNDARY SECTIONS WITH SYMMETRY-RESOLVED INTERMEDIATE GEOMETRY
--
-- Yakir Aharonov, Peter G. Bergmann, Joel L. Lebowitz,
-- "Time Symmetry in the Quantum Process of Measurement".
-- DOI: 10.1103/PhysRev.134.B1410.
--
-- Anup Das, Erfan Zabeh, Bard Ermentrout, Joshua Jacobs,
-- "Planar, spiral, and concentric traveling waves distinguish behavioral
-- states in human memory".
-- DOI: 10.1038/s41467-026-71386-z.
--
-- We import only two-boundary conditioning architecture and finite div/curl-like
-- mode labels.  No retrocausal neural dynamics or quantum cognition is claimed.
------------------------------------------------------------------------

data ModeGeometry : Set where
  sourceLike rotationalLike : ModeGeometry

record IntermediateModeSection : Set where
  constructor intermediateModeSection
  field
    cell : Two.Cell
    geometry : ModeGeometry
    body : Reach.BodyContext
    fromPast : Two.Reach Two.startCell cell
    toFuture : Two.Reach cell Two.goalCell

open IntermediateModeSection public

sourceRoute : IntermediateModeSection
sourceRoute =
  intermediateModeSection
    Two.threatIntermediate
    sourceLike
    Reach.mobilisedContext
    (Two.reachEdge Two.startThreat)
    (Two.reachEdge Two.threatGoal)

rotationalRoute : IntermediateModeSection
rotationalRoute =
  intermediateModeSection
    Two.safeIntermediate
    rotationalLike
    Reach.regulatedContext
    (Two.reachEdge Two.startSafe)
    (Two.reachEdge Two.safeGoal)

sameBoundariesDifferentIntermediateGeometry :
  geometry sourceRoute ≡ geometry rotationalRoute → ⊥
sameBoundariesDifferentIntermediateGeometry ()

sameBoundariesDifferentIntermediateCell :
  cell sourceRoute ≡ cell rotationalRoute → ⊥
sameBoundariesDifferentIntermediateCell ()

routeAccessible : Reach.BodyContext → ModeGeometry → Bool
routeAccessible Reach.regulatedContext sourceLike = true
routeAccessible Reach.regulatedContext rotationalLike = true
routeAccessible Reach.mobilisedContext sourceLike = true
routeAccessible Reach.mobilisedContext rotationalLike = false

mobilisationCanCloseRotationalRouteWithoutDeletingIt :
  routeAccessible Reach.regulatedContext rotationalLike
  ≡ routeAccessible Reach.mobilisedContext rotationalLike → ⊥
mobilisationCanCloseRotationalRouteWithoutDeletingIt ()

sourceRouteStillExistsInCarrier : IntermediateModeSection
sourceRouteStillExistsInCarrier = sourceRoute

rotationalRouteStillExistsInCarrier : IntermediateModeSection
rotationalRouteStillExistsInCarrier = rotationalRoute

record TwoBoundaryModeBoundary : Set where
  constructor twoBoundaryModeBoundary
  field
    sameEndpointsDetermineIntermediateMode : Bool
    bodyGateCanSelectAmongExistingRoutes : Bool
    gatedRouteDeletedFromUnderlyingCarrier : Bool
    futureGoalRetrocausallyForcesNeuralMode : Bool

canonicalTwoBoundaryModeBoundary : TwoBoundaryModeBoundary
canonicalTwoBoundaryModeBoundary =
  twoBoundaryModeBoundary false true false false
