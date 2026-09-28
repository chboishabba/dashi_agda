module DASHI.Reasoning.Trialectic369CechAugmentedCornerStarIndexExact where

------------------------------------------------------------------------
-- AUGMENTED RELATIONAL COVER <-> SELECTED X6 CORNER-STAR INDEX
--
-- DASHI CONTRIBUTION
--
-- The existing relational Grothendieck site has:
--
--   globalABC
--   U_AB, U_BC, U_CA
--   A, B, C
--
-- but no separately typed triple-overlap object.  A selected X6 corner star
-- naturally has:
--
--   one star-global object
--   three incident faces
--   three pairwise incident edges
--   one corner triple overlap.
--
-- Therefore the correct exact indexing comparison is obtained by adding one
-- explicit relational triple-overlap stratum, not by identifying globalABC
-- with the corner.
--
-- This file proves an exact two-sided rechart of the eight strata and their
-- Hasse incidences.  It does NOT identify the augmented index with the full
-- six-face/twelve-edge/eight-corner boundary nerve.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Reasoning.Trialectic369CechCornerStarRecognitionExact as Corner

------------------------------------------------------------------------
-- 1. Eight relational strata: old seven plus an explicit triple overlap.
------------------------------------------------------------------------

data AugmentedRelationalStratum8 : Set where
  relationalGlobal : AugmentedRelationalStratum8
  relationalAB relationalBC relationalCA : AugmentedRelationalStratum8
  relationalOverlapA relationalOverlapB relationalOverlapC :
    AugmentedRelationalStratum8
  relationalTripleABC : AugmentedRelationalStratum8

------------------------------------------------------------------------
-- 2. Eight selected corner-star strata.
------------------------------------------------------------------------

data SelectedCornerStarStratum8 : Set where
  cornerStarGlobal : SelectedCornerStarStratum8
  cornerStarFaceAB cornerStarFaceBC cornerStarFaceCA :
    SelectedCornerStarStratum8
  cornerStarEdgeA cornerStarEdgeB cornerStarEdgeC :
    SelectedCornerStarStratum8
  cornerStarTripleCorner : SelectedCornerStarStratum8

relationalToCornerStar :
  AugmentedRelationalStratum8 ->
  SelectedCornerStarStratum8
relationalToCornerStar relationalGlobal = cornerStarGlobal
relationalToCornerStar relationalAB = cornerStarFaceAB
relationalToCornerStar relationalBC = cornerStarFaceBC
relationalToCornerStar relationalCA = cornerStarFaceCA
relationalToCornerStar relationalOverlapA = cornerStarEdgeA
relationalToCornerStar relationalOverlapB = cornerStarEdgeB
relationalToCornerStar relationalOverlapC = cornerStarEdgeC
relationalToCornerStar relationalTripleABC = cornerStarTripleCorner

cornerStarToRelational :
  SelectedCornerStarStratum8 ->
  AugmentedRelationalStratum8
cornerStarToRelational cornerStarGlobal = relationalGlobal
cornerStarToRelational cornerStarFaceAB = relationalAB
cornerStarToRelational cornerStarFaceBC = relationalBC
cornerStarToRelational cornerStarFaceCA = relationalCA
cornerStarToRelational cornerStarEdgeA = relationalOverlapA
cornerStarToRelational cornerStarEdgeB = relationalOverlapB
cornerStarToRelational cornerStarEdgeC = relationalOverlapC
cornerStarToRelational cornerStarTripleCorner = relationalTripleABC

relationalCornerStarRoundTrip :
  (stratum : AugmentedRelationalStratum8) ->
  cornerStarToRelational (relationalToCornerStar stratum) ≡ stratum
relationalCornerStarRoundTrip relationalGlobal = refl
relationalCornerStarRoundTrip relationalAB = refl
relationalCornerStarRoundTrip relationalBC = refl
relationalCornerStarRoundTrip relationalCA = refl
relationalCornerStarRoundTrip relationalOverlapA = refl
relationalCornerStarRoundTrip relationalOverlapB = refl
relationalCornerStarRoundTrip relationalOverlapC = refl
relationalCornerStarRoundTrip relationalTripleABC = refl

cornerStarRelationalRoundTrip :
  (stratum : SelectedCornerStarStratum8) ->
  relationalToCornerStar (cornerStarToRelational stratum) ≡ stratum
cornerStarRelationalRoundTrip cornerStarGlobal = refl
cornerStarRelationalRoundTrip cornerStarFaceAB = refl
cornerStarRelationalRoundTrip cornerStarFaceBC = refl
cornerStarRelationalRoundTrip cornerStarFaceCA = refl
cornerStarRelationalRoundTrip cornerStarEdgeA = refl
cornerStarRelationalRoundTrip cornerStarEdgeB = refl
cornerStarRelationalRoundTrip cornerStarEdgeC = refl
cornerStarRelationalRoundTrip cornerStarTripleCorner = refl

------------------------------------------------------------------------
-- 3. Hasse incidence on the augmented relational index.
------------------------------------------------------------------------

data RelationalHasseIncidence :
  AugmentedRelationalStratum8 ->
  AugmentedRelationalStratum8 ->
  Set where
  abToGlobal :
    RelationalHasseIncidence relationalAB relationalGlobal
  bcToGlobal :
    RelationalHasseIncidence relationalBC relationalGlobal
  caToGlobal :
    RelationalHasseIncidence relationalCA relationalGlobal

  aToAB :
    RelationalHasseIncidence relationalOverlapA relationalAB
  aToCA :
    RelationalHasseIncidence relationalOverlapA relationalCA
  bToAB :
    RelationalHasseIncidence relationalOverlapB relationalAB
  bToBC :
    RelationalHasseIncidence relationalOverlapB relationalBC
  cToBC :
    RelationalHasseIncidence relationalOverlapC relationalBC
  cToCA :
    RelationalHasseIncidence relationalOverlapC relationalCA

  tripleToA :
    RelationalHasseIncidence relationalTripleABC relationalOverlapA
  tripleToB :
    RelationalHasseIncidence relationalTripleABC relationalOverlapB
  tripleToC :
    RelationalHasseIncidence relationalTripleABC relationalOverlapC

------------------------------------------------------------------------
-- 4. Hasse incidence on the selected corner star.
------------------------------------------------------------------------

data CornerStarHasseIncidence :
  SelectedCornerStarStratum8 ->
  SelectedCornerStarStratum8 ->
  Set where
  faceABToGlobal :
    CornerStarHasseIncidence cornerStarFaceAB cornerStarGlobal
  faceBCToGlobal :
    CornerStarHasseIncidence cornerStarFaceBC cornerStarGlobal
  faceCAToGlobal :
    CornerStarHasseIncidence cornerStarFaceCA cornerStarGlobal

  edgeAToFaceAB :
    CornerStarHasseIncidence cornerStarEdgeA cornerStarFaceAB
  edgeAToFaceCA :
    CornerStarHasseIncidence cornerStarEdgeA cornerStarFaceCA
  edgeBToFaceAB :
    CornerStarHasseIncidence cornerStarEdgeB cornerStarFaceAB
  edgeBToFaceBC :
    CornerStarHasseIncidence cornerStarEdgeB cornerStarFaceBC
  edgeCToFaceBC :
    CornerStarHasseIncidence cornerStarEdgeC cornerStarFaceBC
  edgeCToFaceCA :
    CornerStarHasseIncidence cornerStarEdgeC cornerStarFaceCA

  cornerToEdgeA :
    CornerStarHasseIncidence cornerStarTripleCorner cornerStarEdgeA
  cornerToEdgeB :
    CornerStarHasseIncidence cornerStarTripleCorner cornerStarEdgeB
  cornerToEdgeC :
    CornerStarHasseIncidence cornerStarTripleCorner cornerStarEdgeC

relationalIncidenceToCornerStar :
  {child parent : AugmentedRelationalStratum8} ->
  RelationalHasseIncidence child parent ->
  CornerStarHasseIncidence
    (relationalToCornerStar child)
    (relationalToCornerStar parent)
relationalIncidenceToCornerStar abToGlobal = faceABToGlobal
relationalIncidenceToCornerStar bcToGlobal = faceBCToGlobal
relationalIncidenceToCornerStar caToGlobal = faceCAToGlobal
relationalIncidenceToCornerStar aToAB = edgeAToFaceAB
relationalIncidenceToCornerStar aToCA = edgeAToFaceCA
relationalIncidenceToCornerStar bToAB = edgeBToFaceAB
relationalIncidenceToCornerStar bToBC = edgeBToFaceBC
relationalIncidenceToCornerStar cToBC = edgeCToFaceBC
relationalIncidenceToCornerStar cToCA = edgeCToFaceCA
relationalIncidenceToCornerStar tripleToA = cornerToEdgeA
relationalIncidenceToCornerStar tripleToB = cornerToEdgeB
relationalIncidenceToCornerStar tripleToC = cornerToEdgeC

cornerStarIncidenceToRelational :
  {child parent : SelectedCornerStarStratum8} ->
  CornerStarHasseIncidence child parent ->
  RelationalHasseIncidence
    (cornerStarToRelational child)
    (cornerStarToRelational parent)
cornerStarIncidenceToRelational faceABToGlobal = abToGlobal
cornerStarIncidenceToRelational faceBCToGlobal = bcToGlobal
cornerStarIncidenceToRelational faceCAToGlobal = caToGlobal
cornerStarIncidenceToRelational edgeAToFaceAB = aToAB
cornerStarIncidenceToRelational edgeAToFaceCA = aToCA
cornerStarIncidenceToRelational edgeBToFaceAB = bToAB
cornerStarIncidenceToRelational edgeBToFaceBC = bToBC
cornerStarIncidenceToRelational edgeCToFaceBC = cToBC
cornerStarIncidenceToRelational edgeCToFaceCA = cToCA
cornerStarIncidenceToRelational cornerToEdgeA = tripleToA
cornerStarIncidenceToRelational cornerToEdgeB = tripleToB
cornerStarIncidenceToRelational cornerToEdgeC = tripleToC

relationalIncidenceRoundTrip :
  {child parent : AugmentedRelationalStratum8} ->
  (incidence : RelationalHasseIncidence child parent) ->
  cornerStarIncidenceToRelational
    (relationalIncidenceToCornerStar incidence)
  ≡ incidence
relationalIncidenceRoundTrip abToGlobal = refl
relationalIncidenceRoundTrip bcToGlobal = refl
relationalIncidenceRoundTrip caToGlobal = refl
relationalIncidenceRoundTrip aToAB = refl
relationalIncidenceRoundTrip aToCA = refl
relationalIncidenceRoundTrip bToAB = refl
relationalIncidenceRoundTrip bToBC = refl
relationalIncidenceRoundTrip cToBC = refl
relationalIncidenceRoundTrip cToCA = refl
relationalIncidenceRoundTrip tripleToA = refl
relationalIncidenceRoundTrip tripleToB = refl
relationalIncidenceRoundTrip tripleToC = refl

cornerStarIncidenceRoundTrip :
  {child parent : SelectedCornerStarStratum8} ->
  (incidence : CornerStarHasseIncidence child parent) ->
  relationalIncidenceToCornerStar
    (cornerStarIncidenceToRelational incidence)
  ≡ incidence
cornerStarIncidenceRoundTrip faceABToGlobal = refl
cornerStarIncidenceRoundTrip faceBCToGlobal = refl
cornerStarIncidenceRoundTrip faceCAToGlobal = refl
cornerStarIncidenceRoundTrip edgeAToFaceAB = refl
cornerStarIncidenceRoundTrip edgeAToFaceCA = refl
cornerStarIncidenceRoundTrip edgeBToFaceAB = refl
cornerStarIncidenceRoundTrip edgeBToFaceBC = refl
cornerStarIncidenceRoundTrip edgeCToFaceBC = refl
cornerStarIncidenceRoundTrip edgeCToFaceCA = refl
cornerStarIncidenceRoundTrip cornerToEdgeA = refl
cornerStarIncidenceRoundTrip cornerToEdgeB = refl
cornerStarIncidenceRoundTrip cornerToEdgeC = refl

------------------------------------------------------------------------
-- 5. Geometric realization of the selected star.
------------------------------------------------------------------------

faceABGeometry : Geometry.Face6
faceABGeometry = Corner.localChartFace Corner.localAB

faceBCGeometry : Geometry.Face6
faceBCGeometry = Corner.localChartFace Corner.localBC

faceCAGeometry : Geometry.Face6
faceCAGeometry = Corner.localChartFace Corner.localCA

edgeAGeometry : Nerve.Edge12
edgeAGeometry = Corner.overlapEdge Corner.overlapA

edgeBGeometry : Nerve.Edge12
edgeBGeometry = Corner.overlapEdge Corner.overlapB

edgeCGeometry : Nerve.Edge12
edgeCGeometry = Corner.overlapEdge Corner.overlapC

tripleCornerGeometry : Corners.Corner3
tripleCornerGeometry = Corner.selectedCorner

------------------------------------------------------------------------
-- 6. Firewall: exact augmented corner-star indexing is not the full nerve.
------------------------------------------------------------------------

data AugmentedCornerStarIndexIsFullBoundaryNerve : Set where
data ExistingSevenObjectRelationalSiteAlreadyHadTripleCorner : Set where
data GlobalObjectIsTripleOverlapCorner : Set where

augmentedCornerStarIndexDoesNotBecomeFullBoundaryNerve :
  AugmentedCornerStarIndexIsFullBoundaryNerve -> ⊥
augmentedCornerStarIndexDoesNotBecomeFullBoundaryNerve ()

oldRelationalSiteDidNotAlreadyContainTripleCorner :
  ExistingSevenObjectRelationalSiteAlreadyHadTripleCorner -> ⊥
oldRelationalSiteDidNotAlreadyContainTripleCorner ()

globalObjectStillNotTripleOverlapCorner :
  GlobalObjectIsTripleOverlapCorner -> ⊥
globalObjectStillNotTripleOverlapCorner ()

record Trialectic369CechAugmentedCornerStarIndexBoundary : Set where
  constructor trialectic-369-cech-augmented-corner-star-index-boundary
  field
    explicitTripleOverlapAdded : Bool
    eightStrataRechartExact : Bool
    HasseIncidenceRechartExact : Bool
    globalObjectKeptDistinctFromTripleCorner : Bool
    selectedFacesRealizedInX6Nerve : Bool
    selectedEdgesRealizedInX6Nerve : Bool
    selectedCornerRealizedInX6Nerve : Bool
    fullBoundaryNerveEquivalenceClaimed : Bool

canonicalTrialectic369CechAugmentedCornerStarIndexBoundary :
  Trialectic369CechAugmentedCornerStarIndexBoundary
canonicalTrialectic369CechAugmentedCornerStarIndexBoundary =
  trialectic-369-cech-augmented-corner-star-index-boundary
    true true true true true true true false
