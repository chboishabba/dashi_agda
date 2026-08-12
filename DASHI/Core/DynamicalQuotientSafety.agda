module DASHI.Core.DynamicalQuotientSafety where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability

------------------------------------------------------------------------
-- Dynamic quotient safety.
--
-- A consumer projection is safe for a transition language precisely when
-- projected equality is a congruence for every same-action admissible trace.
-- This is stronger than merely answering one present-time query correctly.
------------------------------------------------------------------------

record DynamicConsumerSafety
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  constructor dynamicConsumerSafety
  field
    traceCongruence :
      ∀ {actions : List Action}
        {left right leftAfter rightAfter : State} →
      project left ≡ project right →
      Reachability.Executes system actions left leftAfter →
      Reachability.Executes system actions right rightAfter →
      project leftAfter ≡ project rightAfter

open DynamicConsumerSafety public

------------------------------------------------------------------------
-- Terminalisation defect.
--
-- The consumer currently identifies two fine states, but the same admissible
-- continuation makes their consumer-visible futures differ.  Therefore the
-- forgotten distinction remained causally relevant to that consumer.
------------------------------------------------------------------------

record TerminalisationDefect
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  constructor terminalisationDefect
  field
    actionTrace : List Action
    left right leftAfter rightAfter : State
    sameCurrentObservation : project left ≡ project right
    leftExecution :
      Reachability.Executes system actionTrace left leftAfter
    rightExecution :
      Reachability.Executes system actionTrace right rightAfter
    futureObservationsDiffer :
      project leftAfter ≡ project rightAfter → ⊥

open TerminalisationDefect public

terminalisationDefectContradictsSafety :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation} →
  DynamicConsumerSafety system project →
  TerminalisationDefect system project →
  ⊥
terminalisationDefectContradictsSafety safety defect =
  futureObservationsDiffer defect
    (traceCongruence safety
      (sameCurrentObservation defect)
      (leftExecution defect)
      (rightExecution defect))

------------------------------------------------------------------------
-- Safety is explicitly consumer-relative: another projection may need to
-- retain more provenance even on the same fine carrier and action system.
------------------------------------------------------------------------

record ConsumerRelativeSafetyBoundary : Set₁ where
  constructor consumerRelativeSafetyBoundary
  field
    State Action ObservationA ObservationB : Set
    system : Dependency.DependentActionSystem State Action
    projectionA : State → ObservationA
    projectionB : State → ObservationB

open ConsumerRelativeSafetyBoundary public
