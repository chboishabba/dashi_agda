module DASHI.Core.TypedTemporalExperimentExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A small typed event/experiment layer combining qualitative interval
-- relations with bounded action traces.
--
-- Source vocabulary:
--   James F. Allen, "Maintaining Knowledge about Temporal Intervals",
--   Communications of the ACM 26(11), 1983,
--   DOI 10.1145/182.358434.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericFuturePartitionRefinementExact as Future
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base

data IntervalRelation : Set where
  before : IntervalRelation
  after : IntervalRelation
  meets : IntervalRelation
  metBy : IntervalRelation
  overlaps : IntervalRelation
  overlappedBy : IntervalRelation
  starts : IntervalRelation
  startedBy : IntervalRelation
  during : IntervalRelation
  contains : IntervalRelation
  finishes : IntervalRelation
  finishedBy : IntervalRelation
  equals : IntervalRelation

record IntervalEvent
    (Time Payload Provenance : Set) : Set₁ where
  constructor intervalEvent
  field
    start : Time
    finish : Time
    payload : Payload
    provenance : Provenance

open IntervalEvent public

record TemporalConstraint
    (Event : Set) : Set where
  constructor temporalConstraint
  field
    left : Event
    right : Event
    allowedRelations : List IntervalRelation
    constraintReference : String

open TemporalConstraint public

record TemporalConstraintNetwork
    (Event : Set) : Set₁ where
  constructor temporalConstraintNetwork
  field
    events : List Event
    constraints : List (TemporalConstraint Event)
    consistencyWitnessReference : String

open TemporalConstraintNetwork public

data EventKind : Set where
  observedEvent : EventKind
  inferredEvent : EventKind
  continuousFlowEvent : EventKind
  discreteJumpEvent : EventKind
  interventionEvent : EventKind

record TypedEvent
    (Time Payload Provenance : Set) : Set₁ where
  constructor typedEvent
  field
    interval : IntervalEvent Time Payload Provenance
    kind : EventKind
    authorityReference : String

open TypedEvent public

Experiment : Set → Set
Experiment Action = List Action

BoundedExperimentEquivalent :
  ∀ {State Action Observation : Set} →
  Nat →
  (State → Observation) →
  (Action → State → State) →
  State → State → Set
BoundedExperimentEquivalent =
  Future.RefinesToDepth

runExperiment :
  ∀ {State Action : Set} →
  (Action → State → State) →
  Experiment Action →
  State → State
runExperiment = Future.run

record ExperimentObservation
    (State Action Observation : Set)
    (observe : State → Observation)
    (step : Action → State → State) : Set₁ where
  constructor experimentObservation
  field
    experiment : Experiment Action
    initialState : State
    finalObservation : Observation
    finalObservationCorrect :
      finalObservation
      ≡ observe (runExperiment step experiment initialState)

open ExperimentObservation public

BoundedExperimentEnumeration :
  ∀ {Action : Set} →
  (Experiment Action → Set) → Set₁
BoundedExperimentEnumeration = Base.BoundedEnumeration

data HybridStepKind : Set where
  continuousStep : HybridStepKind
  discreteStep : HybridStepKind
  observationStep : HybridStepKind

record HybridEventStep
    (State Action : Set) : Set₁ where
  constructor hybridEventStep
  field
    kind : HybridStepKind
    action : Action
    transition : State → State
    semanticsReference : String

open HybridEventStep public

record TypedTemporalExperimentBoundary : Set where
  constructor typedTemporalExperimentBoundary
  field
    intervalRelationDoesNotImplyCausation : Bool
    inferredEventIsNotObservedEvent : Bool
    boundedTraceEquivalenceIsLanguageRelative : Bool
    intervalConstraintsAndStateTransitionsRemainDistinct : Bool
    fullAllenCompositionProcedureNotClaimedHere : Bool
    experimentExhaustionDoesNotProveUnboundedGlobalCompleteness : Bool

open TypedTemporalExperimentBoundary public

canonicalTypedTemporalExperimentBoundary :
  TypedTemporalExperimentBoundary
canonicalTypedTemporalExperimentBoundary =
  typedTemporalExperimentBoundary
    true true true true true true
