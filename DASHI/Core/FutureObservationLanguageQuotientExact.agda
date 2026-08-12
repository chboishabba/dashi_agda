module DASHI.Core.FutureObservationLanguageQuotientExact where

------------------------------------------------------------------------
-- CANONICAL FUTURE-OBSERVATION EQUIVALENCE
--
-- DependentActionSystem is intentionally proof-bearing and may be
-- nondeterministic.  Therefore the canonical consumer semantics is not a
-- hidden deterministic step function.  It is the complete language of
-- observations reachable under each action trace.
--
-- Two states are future-equivalent exactly when those trace-indexed
-- observation languages coincide.  This is an honest equivalence relation
-- without choice, function extensionality, or a determinism axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.TypedDependencyCore as Dependency

record LogicalIff (A B : Set) : Set where
  constructor logicalIff
  field
    forward : A → B
    backward : B → A

open LogicalIff public

------------------------------------------------------------------------
-- A trace-indexed observation is inhabited exactly when some admissible
-- execution of that trace reaches a state exposing that observation.
------------------------------------------------------------------------

data FutureObservation
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (start : State)
    (actions : List Action)
    (observation : Observation) : Set where
  futureObservation :
    (after : State) →
    Reachability.Executes system actions start after →
    project after ≡ observation →
    FutureObservation system project start actions observation

------------------------------------------------------------------------
-- Canonical future language equivalence.
------------------------------------------------------------------------

record FutureObservationEquivalent
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (left right : State) : Set₁ where
  constructor futureObservationEquivalent
  field
    sameFutureLanguage :
      (actions : List Action) →
      (observation : Observation) →
      LogicalIff
        (FutureObservation system project left actions observation)
        (FutureObservation system project right actions observation)

open FutureObservationEquivalent public

futureEquivalentRefl :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    (state : State) →
  FutureObservationEquivalent system project state state
futureEquivalentRefl state =
  futureObservationEquivalent
    (λ actions observation → logicalIff (λ witness → witness) (λ witness → witness))

futureEquivalentSym :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {left right : State} →
  FutureObservationEquivalent system project left right →
  FutureObservationEquivalent system project right left
futureEquivalentSym equivalent =
  futureObservationEquivalent λ actions observation →
    logicalIff
      (backward (sameFutureLanguage equivalent actions observation))
      (forward (sameFutureLanguage equivalent actions observation))

futureEquivalentTrans :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {left middle right : State} →
  FutureObservationEquivalent system project left middle →
  FutureObservationEquivalent system project middle right →
  FutureObservationEquivalent system project left right
futureEquivalentTrans leftMiddle middleRight =
  futureObservationEquivalent λ actions observation →
    logicalIff
      (λ witness →
        forward (sameFutureLanguage middleRight actions observation)
          (forward (sameFutureLanguage leftMiddle actions observation) witness))
      (λ witness →
        backward (sameFutureLanguage leftMiddle actions observation)
          (backward (sameFutureLanguage middleRight actions observation) witness))

------------------------------------------------------------------------
-- Kernel-level universal property.
--
-- A projection is future-language safe exactly when every pair it collapses
-- already belongs to FutureObservationEquivalent.  Thus its kernel is a
-- subrelation of the canonical future-equivalence relation.  Equivalently,
-- FutureObservationEquivalent is the largest relation that may be collapsed
-- without identifying states with distinct consumer-visible future languages.
--
-- This is the constructive relation-level form of the "coarsest safe
-- quotient" theorem.  We deliberately do not manufacture a set quotient:
-- an extensional quotient presentation is a separate representation choice.
------------------------------------------------------------------------

record FutureLanguageSafeProjection
    {State Action Observation Coarse : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (coarsen : State → Coarse) : Set₁ where
  constructor futureLanguageSafeProjection
  field
    kernelContainedInFutureEquivalence :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      FutureObservationEquivalent system project left right

open FutureLanguageSafeProjection public

record KernelSubrelation
    {State Coarse : Set}
    (coarsen : State → Coarse)
    (Relation : State → State → Set₁) : Set₁ where
  constructor kernelSubrelation
  field
    kernelIncluded :
      ∀ {left right} → coarsen left ≡ coarsen right → Relation left right

open KernelSubrelation public

safeProjectionKernelFactorsThroughFutureEquivalence :
  ∀ {State Action Observation Coarse}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : State → Coarse} →
  FutureLanguageSafeProjection system project coarsen →
  KernelSubrelation coarsen (FutureObservationEquivalent system project)
safeProjectionKernelFactorsThroughFutureEquivalence safe =
  kernelSubrelation (kernelContainedInFutureEquivalence safe)

------------------------------------------------------------------------
-- A presentation of the canonical quotient may be supplied by an application
-- when it has a finite code, setoid quotient, trie, automaton state, etc.
-- Equality in that presentation must characterize future equivalence exactly.
------------------------------------------------------------------------

record FutureEquivalencePresentation
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  constructor futureEquivalencePresentation
  field
    QuotientCode : Set
    classOf : State → QuotientCode
    classEqualitySound :
      ∀ {left right} →
      classOf left ≡ classOf right →
      FutureObservationEquivalent system project left right
    classEqualityComplete :
      ∀ {left right} →
      FutureObservationEquivalent system project left right →
      classOf left ≡ classOf right

open FutureEquivalencePresentation public
