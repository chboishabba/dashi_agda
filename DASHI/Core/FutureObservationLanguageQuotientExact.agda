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
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.TypedDependencyCore as Dependency

record LogicalIff (A B : Set) : Set where
  constructor logicalIff
  field
    forward : A → B
    backward : B → A

open LogicalIff public

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
-- Concrete quotient presentations.
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

------------------------------------------------------------------------
-- Actual factorization when a coarse projection supplies a section.
--
-- In intensional Agda, an arbitrary quotient map does not construct a choice
-- of representative.  If an application has an explicit section, however,
-- no choice principle is needed: send each coarse value to the future class of
-- its chosen representative.  Safety makes that definition independent of the
-- fine state from which the coarse value arose.
------------------------------------------------------------------------

record SectionedProjection
    {State Coarse : Set}
    (coarsen : State → Coarse) : Set₁ where
  constructor sectionedProjection
  field
    section : Coarse → State
    sectionRightInverse :
      (coarse : Coarse) → coarsen (section coarse) ≡ coarse

open SectionedProjection public

record FactorizationThroughFutureQuotient
    {State Action Observation Coarse : Set}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : State → Coarse}
    (presentation : FutureEquivalencePresentation system project) : Set₁ where
  constructor factorizationThroughFutureQuotient
  field
    factor : Coarse → QuotientCode presentation
    factorizes :
      (state : State) →
      classOf presentation state ≡ factor (coarsen state)

open FactorizationThroughFutureQuotient public

sectionedSafeProjectionFactors :
  ∀ {State Action Observation Coarse}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {coarsen : State → Coarse}
    (presentation : FutureEquivalencePresentation system project) →
  FutureLanguageSafeProjection system project coarsen →
  SectionedProjection coarsen →
  FactorizationThroughFutureQuotient presentation
sectionedSafeProjectionFactors presentation safe sectioned =
  factorizationThroughFutureQuotient
    (λ coarse → classOf presentation (section sectioned coarse))
    (λ state →
      classEqualityComplete presentation
        (kernelContainedInFutureEquivalence safe
          (sym (sectionRightInverse sectioned (coarsen state)))))
