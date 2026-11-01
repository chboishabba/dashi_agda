module DASHI.Core.FutureObservationalRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- FUTURE OBSERVATIONAL REFINEMENT
--
-- Reference / mathematical ancestor:
--   Ugo Montanari and Vladimiro Sassone,
--   "Dynamic Congruence vs. Progressing Bisimulation for CCS",
--   Fundamenta Informaticae 16(2), 1992.
--   DOI: 10.3233/FI-1992-16206.
--
-- Montanari--Sassone characterize a CCS behavioural equivalence that is both
-- a bisimulation and a congruence under dynamic reconfiguration.  The generic
-- consumer-indexed trace construction below is a DASHI theorem over an
-- application-supplied proof-bearing action system; the citation motivates the
-- congruence problem and does not prove this formulation.
------------------------------------------------------------------------

CurrentEquivalent :
  ∀ {State Observation : Set} →
  (State → Observation) → State → State → Set
CurrentEquivalent project left right = project left ≡ project right

FutureEquivalent :
  ∀ {State Action Observation : Set} →
  (system : Dependency.DependentActionSystem State Action) →
  (project : State → Observation) →
  State → State → Set
FutureEquivalent system project left right =
  ∀ {actions leftAfter rightAfter} →
  Reachability.Executes system actions left leftAfter →
  Reachability.Executes system actions right rightAfter →
  project leftAfter ≡ project rightAfter

futureEquivalentImpliesCurrent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {left right : State} →
  FutureEquivalent system project left right →
  CurrentEquivalent project left right
futureEquivalentImpliesCurrent future =
  future Reachability.executesNil Reachability.executesNil

dynamicSafetyExactlyPromotesCurrentToFuture :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation} →
  Dynamic.DynamicConsumerSafety system project →
  ∀ {left right} →
  CurrentEquivalent project left right →
  FutureEquivalent system project left right
dynamicSafetyExactlyPromotesCurrentToFuture safety same =
  λ leftExecution rightExecution →
    Dynamic.traceCongruence safety same leftExecution rightExecution

------------------------------------------------------------------------
-- Trace concatenation lets future equivalence itself survive prefixes.
------------------------------------------------------------------------

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

composeExecutions :
  ∀ {State Action}
    {system : Dependency.DependentActionSystem State Action}
    {first second : List Action}
    {start middle finish : State} →
  Reachability.Executes system first start middle →
  Reachability.Executes system second middle finish →
  Reachability.Executes system (first ++ second) start finish
composeExecutions Reachability.executesNil secondExecution = secondExecution
composeExecutions
  (Reachability.executesCons admissible rest)
  secondExecution =
  Reachability.executesCons admissible
    (composeExecutions rest secondExecution)

futureEquivalentAfterCommonPrefix :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {left right leftAfter rightAfter : State}
    {prefix : List Action} →
  FutureEquivalent system project left right →
  Reachability.Executes system prefix left leftAfter →
  Reachability.Executes system prefix right rightAfter →
  FutureEquivalent system project leftAfter rightAfter
futureEquivalentAfterCommonPrefix future leftPrefix rightPrefix
  leftSuffix rightSuffix =
  future
    (composeExecutions leftPrefix leftSuffix)
    (composeExecutions rightPrefix rightSuffix)

------------------------------------------------------------------------
-- Coarsest / greatest safe refinement statement.
--
-- A candidate relation is a dynamically congruent refinement of the current
-- quotient if related states are currently projected equal and relatedness is
-- preserved after every common admissible trace.  Every such relation is
-- contained in FutureEquivalent.  FutureEquivalent itself has both properties,
-- so it is the greatest relation satisfying them -- equivalently the coarsest
-- dynamically safe refinement of current observational equality.
------------------------------------------------------------------------

record DynamicallyCongruentRefinement
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation)
    (Related : State → State → Set) : Set₁ where
  constructor dynamicallyCongruentRefinement
  field
    refinesCurrent :
      ∀ {left right} →
      Related left right →
      CurrentEquivalent project left right

    closedUnderCommonTrace :
      ∀ {actions left right leftAfter rightAfter} →
      Related left right →
      Reachability.Executes system actions left leftAfter →
      Reachability.Executes system actions right rightAfter →
      Related leftAfter rightAfter

open DynamicallyCongruentRefinement public

anyCongruentRefinementIsContainedInFutureEquivalent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {Related : State → State → Set} →
  DynamicallyCongruentRefinement system project Related →
  ∀ {left right} →
  Related left right →
  FutureEquivalent system project left right
anyCongruentRefinementIsContainedInFutureEquivalent refinement related
  leftExecution rightExecution =
  refinesCurrent refinement
    (closedUnderCommonTrace refinement related leftExecution rightExecution)

futureEquivalentIsDynamicallyCongruent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation} →
  DynamicallyCongruentRefinement
    system project (FutureEquivalent system project)
futureEquivalentIsDynamicallyCongruent =
  dynamicallyCongruentRefinement
    futureEquivalentImpliesCurrent
    futureEquivalentAfterCommonPrefix

record MaximalSafeRefinement
    {State Action Observation : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) : Set₁ where
  constructor maximalSafeRefinement
  field
    safeRelation : State → State → Set
    safeRelationIsFutureEquivalent :
      ∀ {left right} →
      safeRelation left right →
      FutureEquivalent system project left right
    futureEquivalentIsSafeRelation :
      ∀ {left right} →
      FutureEquivalent system project left right →
      safeRelation left right
    relationIsCongruent :
      DynamicallyCongruentRefinement system project safeRelation
    everyCongruentRefinementFactorsIntoIt :
      ∀ {Related : State → State → Set} →
      DynamicallyCongruentRefinement system project Related →
      ∀ {left right} →
      Related left right → safeRelation left right

open MaximalSafeRefinement public

canonicalMaximalSafeRefinement :
  ∀ {State Action Observation}
    (system : Dependency.DependentActionSystem State Action)
    (project : State → Observation) →
  MaximalSafeRefinement system project
canonicalMaximalSafeRefinement system project =
  maximalSafeRefinement
    (FutureEquivalent system project)
    (λ future → future)
    (λ future → future)
    futureEquivalentIsDynamicallyCongruent
    anyCongruentRefinementIsContainedInFutureEquivalent
