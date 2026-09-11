module DASHI.Applied.RallyReccePaceNoteFibreOverTimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedModelFibreExact as ModelFibre

------------------------------------------------------------------------
-- RALLY RECCE / PACE-NOTE FIBRE OVER TIME
--
-- The road, car, observation bundle and pace-note surface are not collapsed
-- into one state.  The primitive object is a dependent fibre over time and
-- stage position.  Pace notes are observers/encodings of that fibre.
------------------------------------------------------------------------

data Direction : Set where
  left right straight : Direction

-- Semantic severity is intentionally dialect-independent.  Numeric, word,
-- gear/angle and crew-specific systems encode this carrier differently.
data CornerSeverity : Set where
  flat veryFast fast medium tight veryTight square hairpin acute : CornerSeverity

data CornerShape : Set where
  constantRadius tightens opens doubleApex decreasingRadius increasingRadius kink : CornerShape

data LongitudinalFeature : Set where
  level crest brow dip compression jump : LongitudinalFeature

data SurfaceFeature : Set where
  smooth bumpy rough loose gravel mud snow ice tarmac mixedSurface : SurfaceFeature

data LineInstruction : Set where
  neutralLine keepLeft keepRight keepMiddle keepIn keepOut cut smallCut bigCut dontCut early late : LineInstruction

data Hazard : Set where
  caution doubleCaution tripleCaution
  ditch bank rock log post gate bridge tunnel junction water narrowing unseen sudden : Hazard

data LinkKind : Set where
  separated andLink intoLink immediateLink : LinkKind

data DurationClass : Set where
  short halfLong long veryLong extraLong : DurationClass

record PaceNoteSemantic : Set where
  constructor pace-note-semantic
  field
    direction : Direction
    severity : CornerSeverity
    shape : CornerShape
    duration : DurationClass
    longitudinal : LongitudinalFeature
    lineInstruction : LineInstruction
    hazard : Hazard
    linkToNext : LinkKind
    distanceToNextMetres : Nat

open PaceNoteSemantic public

------------------------------------------------------------------------
-- Dialects are encodings, not semantic identities.
------------------------------------------------------------------------

data NoteDialect : Set where
  sixFastestNumeric : NoteDialect
  reversedNumeric : NoteDialect
  extendedNumeric : NoteDialect
  gearBased : NoteDialect
  angleBased : NoteDialect
  descriptiveWords : NoteDialect
  crewSpecific : NoteDialect

record PaceNoteSurface : Set where
  constructor pace-note-surface
  field
    dialect : NoteDialect
    spokenOrWrittenToken : String
    sourceReference : String

open PaceNoteSurface public

record PaceNoteInterpretation : Set where
  constructor pace-note-interpretation
  field
    surface : PaceNoteSurface
    semantic : PaceNoteSemantic
    interpretationReference : String

open PaceNoteInterpretation public

-- A surface token alone does not globally determine severity: e.g. numeric
-- direction and scale conventions vary by system/crew.
data SurfaceTokenGloballyDeterminesSemanticPermission : Set where
surfaceTokenDoesNotGloballyDetermineSemantic :
  SurfaceTokenGloballyDeterminesSemanticPermission → ⊥
surfaceTokenDoesNotGloballyDetermineSemantic ()

------------------------------------------------------------------------
-- Multi-observer recce state.
------------------------------------------------------------------------

data ObserverKind : Set where
  renderedVideo : ObserverKind
  simulatorTelemetry : ObserverKind
  steeringWheel : ObserverKind
  pedals : ObserverKind
  suspensionTravel : ObserverKind
  wheelSpeed : ObserverKind
  inertial : ObserverKind
  pose : ObserverKind
  audioPaceCall : ObserverKind
  privilegedSimulatorGroundTruth : ObserverKind

record ObservationSample : Set where
  constructor observation-sample
  field
    observerKind : ObserverKind
    payloadReference : String
    provenanceReference : String

open ObservationSample public

-- We keep privileged simulator truth as a validation observer, not as an input
-- silently available to a deployable road-state estimator.
data PrivilegedTruthMayLeakIntoDeployableEstimatorPermission : Set where
privilegedTruthDoesNotLeakIntoDeployableEstimator :
  PrivilegedTruthMayLeakIntoDeployableEstimatorPermission → ⊥
privilegedTruthDoesNotLeakIntoDeployableEstimator ()

------------------------------------------------------------------------
-- Native fibre over time and stage station.
------------------------------------------------------------------------

record RallyTemporalFibreSystem : Set₁ where
  field
    Time : Set
    StageStation : Set
    VehicleState : Time → Set
    RoadState : Time → StageStation → Set
    SurfaceState : Time → StageStation → Set
    ControlState : Time → Set
    ObservationState : Time → StageStation → Set
    PaceNoteState : Time → StageStation → Set
    AdmissibleTrajectoryState : Time → StageStation → Set
    timeReference : Time → String
    stationReference : StageStation → String

open RallyTemporalFibreSystem public

record RallyFibreAt
    (system : RallyTemporalFibreSystem)
    (t : Time system)
    (s : StageStation system) : Set₁ where
  constructor rally-fibre-at
  field
    vehicleState : VehicleState system t
    roadState : RoadState system t s
    surfaceState : SurfaceState system t s
    controlState : ControlState system t
    observationState : ObservationState system t s
    paceNoteState : PaceNoteState system t s
    admissibleTrajectoryState : AdmissibleTrajectoryState system t s

open RallyFibreAt public

RallyFibre :
  (system : RallyTemporalFibreSystem) →
  Time system → StageStation system → Set₁
RallyFibre = RallyFibreAt

------------------------------------------------------------------------
-- Repeated traversals refine the live road/surface fibre without requiring
-- road state, vehicle state and observed response to be definitionally equal.
------------------------------------------------------------------------

record RecceTraversal
    (system : RallyTemporalFibreSystem)
    (t : Time system) : Set₁ where
  field
    traversalReference : String
    observedAt : (s : StageStation system) → ObservationState system t s
    calledAt : (s : StageStation system) → PaceNoteState system t s
    controlAt : (s : StageStation system) → ControlState system t

record CrossRunResidual
    (system : RallyTemporalFibreSystem)
    (before after : Time system) : Set₁ where
  field
    ResidualCarrier : Set
    residualAt : StageStation system → ResidualCarrier
    residualReference : String
    residualDoesNotByItselfIdentifyRoadCause : Bool
    residualDoesNotByItselfIdentifyRoadCauseIsTrue :
      residualDoesNotByItselfIdentifyRoadCause ≡ true

------------------------------------------------------------------------
-- Geometry, effective vehicle dynamics and trajectories are separate fibres.
------------------------------------------------------------------------

record LocalRoadSection : Set where
  constructor local-road-section
  field
    geometryReference : String
    centrelineReference : String
    leftExtentReference : String
    rightExtentReference : String
    elevationReference : String
    camberReference : String
    roughnessReference : String
    gripReference : String

record EffectiveVehicleEnvelope : Set where
  constructor effective-vehicle-envelope
  field
    nominalSpecificationReference : String
    identifiedDynamicsReference : String
    setupReference : String
    tyreStateReference : String
    suspensionEnvelopeReference : String
    powerCurveReference : String
    gearingReference : String

-- Same response can remain compatible with multiple hidden physical parameter
-- assignments; identification is an inference fibre, not a magic inversion.
data ObservedResponseUniquelyDeterminesPhysicalParametersPermission : Set where
observedResponseDoesNotForceUniquePhysicalParameters :
  ObservedResponseUniquelyDeterminesPhysicalParametersPermission → ⊥
observedResponseDoesNotForceUniquePhysicalParameters ()

------------------------------------------------------------------------
-- Consumer-indexed optimisation.
------------------------------------------------------------------------

data TrajectoryConsumer : Set where
  competitionMinimumTime : TrajectoryConsumer
  legalRoadMinimumTime : TrajectoryConsumer
  minimumTyreWork : TrajectoryConsumer
  minimumPeakTyreUtilisation : TrajectoryConsumer
  minimumSuspensionLoad : TrajectoryConsumer
  minimumJerk : TrajectoryConsumer
  maximumRobustnessUnderGripUncertainty : TrajectoryConsumer
  informationSeekingRecce : TrajectoryConsumer

data ConstraintKind : Set where
  roadBoundary : ConstraintKind
  competitionBoundary : ConstraintKind
  laneBoundary : ConstraintKind
  speedLimit : ConstraintKind
  giveWayStop : ConstraintKind
  sightDistance : ConstraintKind
  tyreFrictionBudget : ConstraintKind
  suspensionTravelLimit : ConstraintKind
  powertrainEnvelope : ConstraintKind
  steeringEnvelope : ConstraintKind
  uncertaintyMargin : ConstraintKind

record TrajectoryCandidate : Set where
  constructor trajectory-candidate
  field
    trajectoryReference : String
    consumer : TrajectoryConsumer
    constraintsReference : String

-- A fastest legal-road consumer is therefore not an unconstrained racing
-- objective.  Its admissible fibre is indexed by road/lane/rule constraints.
record LegalRoadTrajectoryContract : Set where
  constructor legal-road-trajectory-contract
  field
    objective : TrajectoryConsumer
    objectiveIsLegalMinimumTime : objective ≡ legalRoadMinimumTime
    laneConstraintPresent : Bool
    laneConstraintPresentIsTrue : laneConstraintPresent ≡ true
    speedConstraintPresent : Bool
    speedConstraintPresentIsTrue : speedConstraintPresent ≡ true
    roadRuleConstraintPresent : Bool
    roadRuleConstraintPresentIsTrue : roadRuleConstraintPresent ≡ true

canonicalLegalRoadTrajectoryContract : LegalRoadTrajectoryContract
canonicalLegalRoadTrajectoryContract =
  legal-road-trajectory-contract
    legalRoadMinimumTime refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Recce-to-line compiler contract.
------------------------------------------------------------------------

record RecceToLineCompiler : Set₁ where
  field
    System : RallyTemporalFibreSystem
    GeometryEstimate : Set
    VehicleEstimate : Set
    TrajectoryEstimate : Set

    estimateGeometry :
      (t : Time System) →
      ((s : StageStation System) → ObservationState System t s) →
      ((s : StageStation System) → PaceNoteState System t s) →
      GeometryEstimate

    estimateVehicle :
      (t : Time System) →
      ((s : StageStation System) → ObservationState System t s) →
      VehicleEstimate

    optimise :
      TrajectoryConsumer → GeometryEstimate → VehicleEstimate → TrajectoryEstimate

    compilerReference : String

------------------------------------------------------------------------
-- Existing DASHI machinery is retained as authoritative boundary machinery.
------------------------------------------------------------------------

consumerIndexedModelBoundary : ModelFibre.ConsumerIndexedModelBoundary
consumerIndexedModelBoundary = ModelFibre.canonicalConsumerIndexedModelBoundary

------------------------------------------------------------------------
-- Explicit non-promotions.
------------------------------------------------------------------------

data PaceNoteEqualsMetricGeometryPermission : Set where
data VideoEqualsRoadTruthPermission : Set where
data TelemetryEqualsSurfaceTruthPermission : Set where
data FastestLineEqualsTyreGentlestLinePermission : Set where
data RecceLineEqualsCompetitionLinePermission : Set where
data SimulatorValidationTransfersToRealityPermission : Set where

paceNoteDoesNotEqualMetricGeometry : PaceNoteEqualsMetricGeometryPermission → ⊥
paceNoteDoesNotEqualMetricGeometry ()

videoDoesNotEqualRoadTruth : VideoEqualsRoadTruthPermission → ⊥
videoDoesNotEqualRoadTruth ()

telemetryDoesNotEqualSurfaceTruth : TelemetryEqualsSurfaceTruthPermission → ⊥
telemetryDoesNotEqualSurfaceTruth ()

fastestLineNeedNotEqualTyreGentlestLine : FastestLineEqualsTyreGentlestLinePermission → ⊥
fastestLineNeedNotEqualTyreGentlestLine ()

recceLineNeedNotEqualCompetitionLine : RecceLineEqualsCompetitionLinePermission → ⊥
recceLineNeedNotEqualCompetitionLine ()

simulatorValidationDoesNotAutoTransferToReality : SimulatorValidationTransfersToRealityPermission → ⊥
simulatorValidationDoesNotAutoTransferToReality ()

------------------------------------------------------------------------
-- Source-role receipts for common pace-note families.
------------------------------------------------------------------------

record PaceNoteSourceReceipt : Set where
  constructor pace-note-source-receipt
  field
    sourceTitle : String
    sourceReference : String
    supportsDialectPlurality : Bool
    supportsDialectPluralityIsTrue : supportsDialectPlurality ≡ true
    supportsModifierGrammar : Bool
    supportsModifierGrammarIsTrue : supportsModifierGrammar ≡ true

numericAndDescriptiveSourceReceipt : PaceNoteSourceReceipt
numericAndDescriptiveSourceReceipt =
  pace-note-source-receipt
    "RallySport Magazine: Pacenotes explained with Brendan Reeves"
    "https://rallysportmag.com/video-pace-notes-explained-brendan-reeves-hyundai-i30-n/"
    true refl
    true refl

codemastersCallSystemSourceReceipt : PaceNoteSourceReceipt
codemastersCallSystemSourceReceipt =
  pace-note-source-receipt
    "Dirt Rally pace-note transcription / Codemasters call-system archaeology"
    "https://github.com/maxbechtold/dirt-rally-pace-notes"
    true refl
    true refl

record RallyRecceBoundary : Set where
  constructor rally-recce-boundary
  field
    stateIsFibreOverTimeAndStation : Bool
    stateIsFibreOverTimeAndStationIsTrue : stateIsFibreOverTimeAndStation ≡ true
    paceNotesAreObserversNotRoadTruth : Bool
    paceNotesAreObserversNotRoadTruthIsTrue : paceNotesAreObserversNotRoadTruth ≡ true
    numericDialectIsUniversal : Bool
    numericDialectIsUniversalIsFalse : numericDialectIsUniversal ≡ false
    optimisationIsConsumerIndexed : Bool
    optimisationIsConsumerIndexedIsTrue : optimisationIsConsumerIndexed ≡ true

canonicalRallyRecceBoundary : RallyRecceBoundary
canonicalRallyRecceBoundary =
  rally-recce-boundary true refl true refl false refl true refl
