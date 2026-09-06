module DASHI.Core.AskListenObservationProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryFibreAddedCoordinateProducerBidiExact as Added
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Core.ExperimentalCoordinateDesignExact as Design
import DASHI.Core.BidiResidualApproximationExact as Bidi

------------------------------------------------------------------------
-- ASK / LISTEN -> OBSERVATION PRODUCER
--
-- Ask/listen/deliberate are not magical epistemic moves.  When they are used to
-- refine a compatible fibre, they must be tied to an observation coordinate
-- that actually separates a current collision and has its own calibration.
------------------------------------------------------------------------

data DialogicObservationKind : Set where
  askObservation
  listenObservation
  deliberateObservation
  : DialogicObservationKind

asExtendedMove : DialogicObservationKind → Delib.ExtendedMoveKind
asExtendedMove askObservation = Delib.askMove
asExtendedMove listenObservation = Delib.listenMove
asExtendedMove deliberateObservation = Delib.deliberateMove

record DialogicObservationProducer
    {QueryT State Hidden Answer Control Value Dimension ExistingCode : Set}
    {problem : Added.Query.QueryCompatibleProblem QueryT State Hidden Answer}
    {query : QueryT} {state : State}
    (collision : Added.QueryFibreCollision problem query state)
    (design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension)
    (existing : Hidden → ExistingCode) : Set₁ where
  constructor dialogic-observation-producer
  field
    kind : DialogicObservationKind
    addedCoordinate : Added.AddedCoordinateProducer collision design existing
    participantOrSourceReference : String
    calibrationReference : String
    authorityReference : String

open DialogicObservationProducer public

dialogicMoveKind :
  ∀ {QueryT State Hidden Answer Control Value Dimension ExistingCode : Set}
    {problem : Added.Query.QueryCompatibleProblem QueryT State Hidden Answer}
    {query : QueryT} {state : State}
    {collision : Added.QueryFibreCollision problem query state}
    {design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension}
    {existing : Hidden → ExistingCode} →
  DialogicObservationProducer collision design existing →
  Delib.ExtendedMoveKind
dialogicMoveKind producer = asExtendedMove (kind producer)

dialogicObservationRefinesQueryFibre :
  ∀ {QueryT State Hidden Answer Control Value Dimension ExistingCode : Set}
    {problem : Added.Query.QueryCompatibleProblem QueryT State Hidden Answer}
    {query : QueryT} {state : State}
    {collision : Added.QueryFibreCollision problem query state}
    {design : Design.ExperimentalCoordinateDesign Hidden Control Value Dimension}
    {existing : Hidden → ExistingCode}
    (producer : DialogicObservationProducer collision design existing)
    (observed : Value) →
  Bidi.FibreRefines
    (Added.MeasuredQueryFibre problem query state design
      (Design.coordinate (Added.separator (addedCoordinate producer))) observed)
    (Added.Query.queryResidualFibre problem query state)
dialogicObservationRefinesQueryFibre producer observed =
  Added.addedCoordinateAlwaysRefinesQueryFibre
    _ _ _ _
    (Design.coordinate (Added.separator (addedCoordinate producer)))
    observed

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data AskingAloneSeparatesCollision : Set where
data ListeningAutomaticallyTransfersAuthority : Set where
data DeliberationAutomaticallyCreatesCalibratedMeasurement : Set where

askingAloneDoesNotSeparateCollision : AskingAloneSeparatesCollision → ⊥
askingAloneDoesNotSeparateCollision ()

listeningDoesNotAutomaticallyTransferAuthority :
  ListeningAutomaticallyTransfersAuthority → ⊥
listeningDoesNotAutomaticallyTransferAuthority ()

deliberationDoesNotAutomaticallyCreateCalibration :
  DeliberationAutomaticallyCreatesCalibratedMeasurement → ⊥
deliberationDoesNotAutomaticallyCreateCalibration ()

record AskListenObservationBoundary : Set where
  constructor ask-listen-observation-boundary
  field
    dialogicMoveNeedsSeparatingCoordinate : Bool
    dialogicObservationMayRefineFibre : Bool
    askListenAloneIsMeasurementProof : Bool
    listeningTransfersAuthority : Bool

canonicalAskListenObservationBoundary : AskListenObservationBoundary
canonicalAskListenObservationBoundary =
  ask-listen-observation-boundary true true false false
