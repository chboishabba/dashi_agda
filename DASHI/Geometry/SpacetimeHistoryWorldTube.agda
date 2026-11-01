module DASHI.Geometry.SpacetimeHistoryWorldTube where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Candidate-only spacetime-history geometry.
--
-- A recorded history is treated as a time-indexed spatial trajectory.  The
-- entire trajectory is the 3+1-dimensional history carrier; visual outputs
-- are explicit projections and never identified with the underlying history.
-- GPS samples remain uncertain observations rather than exact positions.

data Never : Set where

data HistoryRoute : Set where
  candidateGeometryRoute : HistoryRoute
  exactLocationRecoveryRoute : HistoryRoute
  completeLifeRecoveryRoute : HistoryRoute
  projectionEqualsHistoryRoute : HistoryRoute
  surveillanceAuthorityRoute : HistoryRoute

AdmissibleHistoryRoute : HistoryRoute → Set
AdmissibleHistoryRoute candidateGeometryRoute = ⊤
AdmissibleHistoryRoute exactLocationRecoveryRoute = Never
AdmissibleHistoryRoute completeLifeRecoveryRoute = Never
AdmissibleHistoryRoute projectionEqualsHistoryRoute = Never
AdmissibleHistoryRoute surveillanceAuthorityRoute = Never

exactLocationRecoveryRejected :
  AdmissibleHistoryRoute exactLocationRecoveryRoute → Never
exactLocationRecoveryRejected impossible = impossible

completeLifeRecoveryRejected :
  AdmissibleHistoryRoute completeLifeRecoveryRoute → Never
completeLifeRecoveryRejected impossible = impossible

projectionEqualsHistoryRejected :
  AdmissibleHistoryRoute projectionEqualsHistoryRoute → Never
projectionEqualsHistoryRejected impossible = impossible

surveillanceAuthorityRejected :
  AdmissibleHistoryRoute surveillanceAuthorityRoute → Never
surveillanceAuthorityRejected impossible = impossible

data MotionMode : Set where
  stationaryMode : MotionMode
  walkingMode : MotionMode
  cyclingMode : MotionMode
  vehicleMode : MotionMode
  transitMode : MotionMode
  flightMode : MotionMode
  unknownMode : MotionMode

data ProjectionKind : Set where
  spacetimeCubeProjection : ProjectionKind
  geographicLongExposureProjection : ProjectionKind
  calendricalHelixProjection : ProjectionKind
  semanticPlaceBraidProjection : ProjectionKind
  movingPresentSliceProjection : ProjectionKind

record SpatialSample : Set where
  constructor mkSpatialSample
  field
    eastCoordinate : Nat
    northCoordinate : Nat
    altitudeCoordinate : Nat
    coordinateReference : String
open SpatialSample public

record TimelineObservation : Set where
  constructor mkTimelineObservation
  field
    observationIndex : Nat
    observationTime : Nat
    observationPlaceLabel : String
    observationPosition : SpatialSample
    observationUncertaintyRadius : Nat
    observationMotionMode : MotionMode
    observationSource : String
    observationIsExact : Bool
    observationIsExactIsFalse : observationIsExact ≡ false
open TimelineObservation public

mkUncertainTimelineObservation :
  Nat → Nat → String → SpatialSample → Nat → MotionMode → String →
  TimelineObservation
mkUncertainTimelineObservation index time place position uncertainty mode source =
  mkTimelineObservation
    index time place position uncertainty mode source false refl

record WorldTubeSection : Set where
  constructor mkWorldTubeSection
  field
    sectionObservation : TimelineObservation
    sectionSpatialRadius : Nat
    sectionTemporalThickness : Nat
    sectionMeaningWeight : Nat
open WorldTubeSection public

record SpacetimeHistory : Set where
  constructor mkSpacetimeHistory
  field
    historySubject : String
    historyCoordinateReference : String
    historyObservations : List TimelineObservation
    historyWorldTube : List WorldTubeSection
    historyCandidateOnly : Bool
    historyCandidateOnlyIsTrue : historyCandidateOnly ≡ true
    historyCompleteLifeRecovery : Bool
    historyCompleteLifeRecoveryIsFalse : historyCompleteLifeRecovery ≡ false
open SpacetimeHistory public

record ProjectionContract : Set where
  constructor mkProjectionContract
  field
    projectionKind : ProjectionKind
    projectionName : String
    projectionSpatialAxes : String
    projectionTimeEncoding : String
    projectionThicknessEncoding : String
    projectionColourEncoding : String
    projectionPreservesAllCoordinates : Bool
    projectionPreservesAllCoordinatesIsFalse :
      projectionPreservesAllCoordinates ≡ false
    projectionClaim : String
open ProjectionContract public

mkLossyProjectionContract :
  ProjectionKind → String → String → String → String → String → String →
  ProjectionContract
mkLossyProjectionContract kind name spatial time thickness colour claim =
  mkProjectionContract
    kind name spatial time thickness colour false refl claim

canonicalProjectionContracts : List ProjectionContract
canonicalProjectionContracts =
  mkLossyProjectionContract
    spacetimeCubeProjection
    "spacetime cube"
    "east × north"
    "vertical axis"
    "uncertainty or duration"
    "mode, period, or semantic context"
    "A 3D projection of a 3+1 history carrier"
  ∷ mkLossyProjectionContract
    geographicLongExposureProjection
    "geographic long exposure"
    "east × north"
    "integrated into density or brightness"
    "kernel radius"
    "time or visit density"
    "Time is collapsed rather than retained as an independent axis"
  ∷ mkLossyProjectionContract
    calendricalHelixProjection
    "calendrical helix"
    "geography with a cyclic offset"
    "phase plus longitudinal calendar axis"
    "duration or uncertainty"
    "cycle, year, or activity"
    "Repeated routines align while chronology remains partially ordered"
  ∷ mkLossyProjectionContract
    semanticPlaceBraidProjection
    "semantic place braid"
    "clustered place strands"
    "ordering along strands"
    "time spent or confidence"
    "place class or life period"
    "Coordinate detail is quotiented into explicit semantic places"
  ∷ mkLossyProjectionContract
    movingPresentSliceProjection
    "moving present slice"
    "current spatial section"
    "slice parameter"
    "current uncertainty neighbourhood"
    "current context"
    "The experienced present is represented as a section of the full history"
  ∷ []

record PresentSlice : Set where
  constructor mkPresentSlice
  field
    sliceTime : Nat
    sliceVisibleSections : List WorldTubeSection
    sliceIsWholeHistory : Bool
    sliceIsWholeHistoryIsFalse : sliceIsWholeHistory ≡ false
open PresentSlice public

mkPresentSliceOf : Nat → List WorldTubeSection → PresentSlice
mkPresentSliceOf time sections = mkPresentSlice time sections false refl

canonicalWorldTubeNotes : List String
canonicalWorldTubeNotes =
  "The base carrier is position indexed by time"
  ∷ "A world-tube thickens the ideal worldline by uncertainty, duration, or chosen meaning weight"
  ∷ "A horizontal present slice is not the entire history"
  ∷ "A map view is a projection that collapses or encodes time"
  ∷ "Repeated routes may form sheets, trunks, loops, or braids"
  ∷ "Missing samples remain missing rather than being silently reconstructed"
  ∷ "Recorded movement is not a complete account of experience"
  ∷ []
