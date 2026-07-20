module DASHI.Environment.SpatialTransport where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_≤_)

------------------------------------------------------------------------
-- GIS entities and topology.

data SpatialKind : Set where
  rasterCell : SpatialKind
  parcel : SpatialKind
  catchment : SpatialKind
  waterbody : SpatialKind
  streamReach : SpatialKind
  groundwaterZone : SpatialKind
  roadSegment : SpatialKind
  habitatPatch : SpatialKind
  interventionFootprint : SpatialKind

record SpatialNode : Set where
  constructor mkSpatialNode
  field
    nodeId : String
    kind : SpatialKind
    crsLabel : String
    geometryReference : String
    sourceDataset : String
open SpatialNode public

data TransportKind : Set where
  surfaceWater : TransportKind
  groundwater : TransportKind
  sediment : TransportKind
  dissolvedNitrogen : TransportKind
  dissolvedPhosphorus : TransportKind
  pollen : TransportKind
  animalMovement : TransportKind
  seedDispersal : TransportKind
  machineryAccess : TransportKind
  humanAccess : TransportKind

record TimeWindow : Set where
  constructor mkTimeWindow
  field
    startsAt : Nat
    endsAt : Nat
    ordered : startsAt ≤ endsAt
open TimeWindow public

record TransportEdge (from to : SpatialNode) : Set where
  constructor mkTransportEdge
  field
    transport : TransportKind
    activeWindow : TimeWindow
    directionVerified : Bool
    capacityOrConductanceRecorded : Bool
    evidenceReference : String
    uncertaintyReference : String
open TransportEdge public

------------------------------------------------------------------------
-- A path is a typed chain of physically recorded edges.

data Path : SpatialNode → SpatialNode → Set where
  here : ∀ {x} → Path x x
  step :
    ∀ {x y z} →
    TransportEdge x y →
    Path y z →
    Path x z

reachable : SpatialNode → SpatialNode → Set
reachable = Path

pathAppend : ∀ {x y z} → Path x y → Path y z → Path x z
pathAppend here q = q
pathAppend (step e p) q = step e (pathAppend p q)

reachabilityReflexive : ∀ x → reachable x x
reachabilityReflexive x = here

reachabilityTransitive :
  ∀ {x y z} →
  reachable x y →
  reachable y z →
  reachable x z
reachabilityTransitive = pathAppend

------------------------------------------------------------------------
-- Spatial support and temporal compatibility are witnesses, not booleans.

record SpatialSupport (processSource processTarget : SpatialNode) : Set where
  constructor mkSpatialSupport
  field
    physicalPath : Path processSource processTarget
    sourceFootprintRecorded : String
    targetFootprintRecorded : String
    scaleCompatible : Bool
open SpatialSupport public

record TemporalOverlap (sourceWindow targetWindow : TimeWindow) : Set where
  constructor mkTemporalOverlap
  field
    sourceStartsBeforeTargetEnds : startsAt sourceWindow ≤ endsAt targetWindow
    targetStartsBeforeSourceEnds : startsAt targetWindow ≤ endsAt sourceWindow
open TemporalOverlap public

record SourceToObservationWitness
       (source observation : SpatialNode) : Set where
  constructor mkSourceToObservationWitness
  field
    support : SpatialSupport source observation
    transportMechanism : TransportKind
    temporalEvidence : String
    timingCompatible : Bool
    attenuationModelRecorded : Bool
    provenance : List String
open SourceToObservationWitness public

------------------------------------------------------------------------
-- Operational access is a separate graph from ecological transport.

record MachineryProfile : Set where
  constructor mkMachineryProfile
  field
    machineryName : String
    maximumSlopeBasisPoints : Nat
    turningRadiusMillimetres : Nat
    widthMillimetres : Nat
    wetSoilAccessAllowed : Bool
    fuelModelReference : String
open MachineryProfile public

record MachineryRoute
       (machine : MachineryProfile)
       (origin target : SpatialNode) : Set where
  constructor mkMachineryRoute
  field
    accessPath : Path origin target
    slopeConstraintChecked : Bool
    turningConstraintChecked : Bool
    widthConstraintChecked : Bool
    seasonalAccessChecked : Bool
open MachineryRoute public

record SpatialTransportBoundary : Set where
  constructor mkSpatialTransportBoundary
  field
    mapAdjacencyIsNotTransportProof : Bool
    pathRequiresDirectedEdges : Bool
    temporalOverlapMustBeChecked : Bool
    differentTransportMediaRemainDistinct : Bool
    machineryAccessIsNotEcologicalConnectivity : Bool
    missingEdgesRemainPossible : Bool
open SpatialTransportBoundary public

canonicalSpatialTransportBoundary : SpatialTransportBoundary
canonicalSpatialTransportBoundary =
  mkSpatialTransportBoundary true true true true true true
