{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.RequestedFibreSemanticStratumExact where

------------------------------------------------------------------------
-- Semantic incidence over the existing 27-cube stratification.
--
-- Geometry alone deliberately has no semantic authority.  This owner preserves
-- that firewall and adds the missing proof-bearing bridge: each requested fine
-- coordinate receives an application-supplied interpretation of its observed
-- SSP trit, and only then may a centre/face/edge/corner carry semantic content.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Cognition.PNF.HypercomplexRequestedFractranComponentExact as Fine

record ComponentInterpretation
    (component : Fine.RequestedFractranComponent) : Set₁ where
  constructor componentInterpretation
  field
    Meaning : Trit.SSPTrit → Set

open ComponentInterpretation public

record InterpretedRequestedCubie3 : Set₁ where
  constructor interpretedRequestedCubie3
  field
    cubie : Fine.RequestedCubie3

    xInterpretation : ComponentInterpretation (Fine.xComponent cubie)
    yInterpretation : ComponentInterpretation (Fine.yComponent cubie)
    zInterpretation : ComponentInterpretation (Fine.zComponent cubie)

    xMeaning :
      Meaning xInterpretation
        (Fine.observeFine (Fine.xComponent cubie) (Fine.xState cubie))
    yMeaning :
      Meaning yInterpretation
        (Fine.observeFine (Fine.yComponent cubie) (Fine.yState cubie))
    zMeaning :
      Meaning zInterpretation
        (Fine.observeFine (Fine.zComponent cubie) (Fine.zState cubie))

open InterpretedRequestedCubie3 public

interpretedAddress : InterpretedRequestedCubie3 → Geometry.Ternary27Point
interpretedAddress interpreted = Fine.coarseAddress (cubie interpreted)

interpretedStratum : InterpretedRequestedCubie3 → Strata.VoxelStratum
interpretedStratum interpreted = Strata.voxelStratum (interpretedAddress interpreted)

record SemanticCentreWitness
    (interpreted : InterpretedRequestedCubie3) : Set₁ where
  constructor semanticCentreWitness
  field
    geometryIsCentre : interpretedStratum interpreted ≡ Strata.centreStratum
    SemanticCentreMeaning : Set
    semanticMeaning : SemanticCentreMeaning

open SemanticCentreWitness public

record SemanticFaceWitness
    (interpreted : InterpretedRequestedCubie3) : Set₁ where
  constructor semanticFaceWitness
  field
    geometryIsFaceCentre :
      interpretedStratum interpreted ≡ Strata.faceCentreStratum
    SemanticFaceMeaning : Set
    semanticMeaning : SemanticFaceMeaning

open SemanticFaceWitness public

record SemanticEdgeWitness
    (interpreted : InterpretedRequestedCubie3) : Set₁ where
  constructor semanticEdgeWitness
  field
    geometryIsEdgeCentre :
      interpretedStratum interpreted ≡ Strata.edgeCentreStratum
    SemanticEdgeMeaning : Set
    semanticMeaning : SemanticEdgeMeaning

open SemanticEdgeWitness public

record SemanticCornerWitness
    (interpreted : InterpretedRequestedCubie3) : Set₁ where
  constructor semanticCornerWitness
  field
    geometryIsCorner : interpretedStratum interpreted ≡ Strata.cornerStratum
    SemanticCornerMeaning : Set
    semanticMeaning : SemanticCornerMeaning

open SemanticCornerWitness public

record SemanticNamedFaceWitness
    (interpreted : InterpretedRequestedCubie3) : Set₁ where
  constructor semanticNamedFaceWitness
  field
    face : Geometry.Face6
    geometricIncidence : Geometry.OnFace face (interpretedAddress interpreted)
    SemanticIncidenceMeaning : Set
    incidenceMeaning : SemanticIncidenceMeaning

open SemanticNamedFaceWitness public

record SemanticStratumBoundary : Set where
  constructor semanticStratumBoundary
  field
    geometryAloneDeterminesSemanticMeaning : Bool
    typedCoordinateInterpretationRequired : Bool
    namedFaceMayReceiveTypedMeaning : Bool
    edgeMeaningRequiresApplicationWitness : Bool
    cornerMeaningRequiresApplicationWitness : Bool
    semanticMeaningMayBeTransportedOnlyByTypedLaw : Bool

canonicalSemanticStratumBoundary : SemanticStratumBoundary
canonicalSemanticStratumBoundary =
  semanticStratumBoundary false true true true true true
