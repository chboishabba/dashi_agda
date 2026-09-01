{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.RequestedFibreSemanticIncidenceTransportExact where

------------------------------------------------------------------------
-- Generic semantic incidence calculus for the 27-cube.
--
-- The raw Base369 geometry already knows that nearest-neighbour transport
-- changes exactly one ternary coordinate through -1 <-> 0 <-> +1.  The missing
-- semantic layer is to make that one-coordinate change carry an explicit typed
-- resolution/reopening law rather than treating geometry as semantic authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Cognition.PNF.RequestedFibreSemanticStratumExact as Semantic

data IncidenceDirection : Set where
  resolveOneCoordinate reopenOneCoordinate : IncidenceDirection

record TypedIncidenceTransport
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor typedIncidenceTransport
  field
    geometricStep :
      Geometry.HypervoxelAdjacent
        (Semantic.interpretedAddress before)
        (Semantic.interpretedAddress after)
    direction : IncidenceDirection
    SemanticTransportLaw : Set
    semanticTransportLaw : SemanticTransportLaw

open TypedIncidenceTransport public

record CentreToFaceResolution
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor centreToFaceResolution
  field
    transport : TypedIncidenceTransport before after
    directionIsResolution : direction transport ≡ resolveOneCoordinate
    beforeIsCentre :
      Semantic.interpretedStratum before ≡ Strata.centreStratum
    afterIsFace :
      Semantic.interpretedStratum after ≡ Strata.faceCentreStratum

open CentreToFaceResolution public

record FaceToEdgeResolution
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor faceToEdgeResolution
  field
    transport : TypedIncidenceTransport before after
    directionIsResolution : direction transport ≡ resolveOneCoordinate
    beforeIsFace :
      Semantic.interpretedStratum before ≡ Strata.faceCentreStratum
    afterIsEdge :
      Semantic.interpretedStratum after ≡ Strata.edgeCentreStratum

open FaceToEdgeResolution public

record EdgeToCornerResolution
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor edgeToCornerResolution
  field
    transport : TypedIncidenceTransport before after
    directionIsResolution : direction transport ≡ resolveOneCoordinate
    beforeIsEdge :
      Semantic.interpretedStratum before ≡ Strata.edgeCentreStratum
    afterIsCorner :
      Semantic.interpretedStratum after ≡ Strata.cornerStratum

open EdgeToCornerResolution public

record CornerToEdgeReopening
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor cornerToEdgeReopening
  field
    transport : TypedIncidenceTransport before after
    directionIsReopening : direction transport ≡ reopenOneCoordinate
    beforeIsCorner :
      Semantic.interpretedStratum before ≡ Strata.cornerStratum
    afterIsEdge :
      Semantic.interpretedStratum after ≡ Strata.edgeCentreStratum

open CornerToEdgeReopening public

record EdgeToFaceReopening
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor edgeToFaceReopening
  field
    transport : TypedIncidenceTransport before after
    directionIsReopening : direction transport ≡ reopenOneCoordinate
    beforeIsEdge :
      Semantic.interpretedStratum before ≡ Strata.edgeCentreStratum
    afterIsFace :
      Semantic.interpretedStratum after ≡ Strata.faceCentreStratum

open EdgeToFaceReopening public

record FaceToCentreReopening
    (before after : Semantic.InterpretedRequestedCubie3) : Set₁ where
  constructor faceToCentreReopening
  field
    transport : TypedIncidenceTransport before after
    directionIsReopening : direction transport ≡ reopenOneCoordinate
    beforeIsFace :
      Semantic.interpretedStratum before ≡ Strata.faceCentreStratum
    afterIsCentre :
      Semantic.interpretedStratum after ≡ Strata.centreStratum

open FaceToCentreReopening public

------------------------------------------------------------------------
-- Semantic meaning still comes from the typed law, not the direction label.
-- In particular, "corner" means all three requested coordinates are exposed in
-- this chart, not truth, goodness, certainty, or publication authority.
------------------------------------------------------------------------

record SemanticIncidenceBoundary : Set where
  constructor semanticIncidenceBoundary
  field
    adjacencyAloneGrantsSemanticTransport : Bool
    resolutionRequiresTypedLaw : Bool
    reopeningRequiresTypedLaw : Bool
    cornerMeansAbsoluteTruth : Bool
    centreToFaceMayRepresentOneResolvedQuestion : Bool
    cornerToEdgeMayRepresentOneReopenedQuestion : Bool

canonicalSemanticIncidenceBoundary : SemanticIncidenceBoundary
canonicalSemanticIncidenceBoundary =
  semanticIncidenceBoundary false true true false true true
