module DASHI.Core.DynamicalQuotientSafety where

------------------------------------------------------------------------
-- REFERENCE / MOTIVATION
--
-- Patrick Cousot and Radhia Cousot,
-- "Abstract interpretation: a unified lattice model for static analysis of
-- programs by construction or approximation of fixpoints", POPL 1977,
-- pp. 238-252. DOI: 10.1145/512950.512973.
--
-- The reference motivates abstraction/concrete-semantics separation.  The
-- consumer-relative trace-congruence theorem below is the DASHI construction;
-- the citation is not used as proof authority for this exact formulation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability

------------------------------------------------------------------------
-- Dynamic quotient safety.
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
-- Composition warning and valid theorem.
--
-- Dynamic safety is NOT closed under arbitrary post-composition.  A coarser
-- observer may identify two current mid-states whose future observations later
-- diverge.  Post-composition is safe without another dynamical proof when the
-- observer is injective; genuinely coarser second quotients require their own
-- congruence theorem.
------------------------------------------------------------------------

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

postcomposeInjectiveObservationSafety :
  ∀ {State Action Mid Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Mid} →
  DynamicConsumerSafety system project →
  (observe : Mid → Observation) →
  Injective observe →
  DynamicConsumerSafety system (λ state → observe (project state))
postcomposeInjectiveObservationSafety safety observe observeInjective =
  dynamicConsumerSafety λ same leftRun rightRun →
    cong observe
      (traceCongruence safety
        (observeInjective same)
        leftRun
        rightRun)

------------------------------------------------------------------------
-- Terminalisation defect.
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
-- Unsafe collapse versus terminalising/unreopenable collapse.
------------------------------------------------------------------------

record ReopeningScheme
    {State Observation : Set}
    (project : State → Observation) : Set₁ where
  field
    Receipt : Set
    receipt : State → Receipt
    reopen : Observation → Receipt → State
    reopenExact :
      (state : State) →
      reopen (project state) (receipt state) ≡ state

open ReopeningScheme public

record UnreopenableDynamicCollapse
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  field
    dynamicDefect : TerminalisationDefect system project
    AdmissibleReceiptCarrier : Set → Set
    noAdmissibleExactReopening :
      (scheme : ReopeningScheme project) →
      AdmissibleReceiptCarrier (Receipt scheme) →
      ⊥

open UnreopenableDynamicCollapse public

------------------------------------------------------------------------
-- Safety is explicitly consumer-relative.
------------------------------------------------------------------------

record ConsumerRelativeSafetyBoundary : Set₁ where
  constructor consumerRelativeSafetyBoundary
  field
    State Action ObservationA ObservationB : Set
    system : Dependency.DependentActionSystem State Action
    projectionA : State → ObservationA
    projectionB : State → ObservationB

open ConsumerRelativeSafetyBoundary public
