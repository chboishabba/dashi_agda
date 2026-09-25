module DASHI.Core.FutureSafeCoarseFibreCapacityExact where

------------------------------------------------------------------------
-- FUTURE-SAFE COARSE-FIBRE CAPACITY
--
-- FutureObservationalRefinement already proves that FutureEquivalent is the
-- greatest dynamically congruent relation contained in current observational
-- equality -- equivalently, the coarsest dynamically safe relational
-- refinement of the current observer.
--
-- GeneralResidualFibreCardinalityExact already proves that a future-safe
-- residual must inject finite future-distinct representatives inside one coarse
-- fibre.
--
-- This module only composes those two owners:
--
--   current coarse fibre
--       -> quotient relationally by FutureEquivalent
--       -> retain enough residual capacity to distinguish the surviving
--          future-distinct classes.
--
-- No new quotient implementation or cardinality calculus is introduced.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.ResidualFibreLowerBoundExact as Lower
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality

------------------------------------------------------------------------
-- 1. Canonical future relation and maximality.
------------------------------------------------------------------------

CanonicalFutureRelation :
  ∀ {State Action Observation : Set} ->
  Dependency.DependentActionSystem State Action ->
  (State -> Observation) ->
  State -> State -> Set
CanonicalFutureRelation system project =
  Future.FutureEquivalent system project

canonicalFutureRelationRefinesCurrent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {left right : State} ->
  CanonicalFutureRelation system project left right ->
  Future.CurrentEquivalent project left right
canonicalFutureRelationRefinesCurrent =
  Future.futureEquivalentImpliesCurrent

canonicalFutureRelationIsDynamicallyCongruent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation} ->
  Future.DynamicallyCongruentRefinement
    system project (CanonicalFutureRelation system project)
canonicalFutureRelationIsDynamicallyCongruent =
  Future.futureEquivalentIsDynamicallyCongruent

everyDynamicallyCongruentRefinementContainedInCanonical :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {Related : State -> State -> Set} ->
  Future.DynamicallyCongruentRefinement system project Related ->
  ∀ {left right} ->
  Related left right ->
  CanonicalFutureRelation system project left right
everyDynamicallyCongruentRefinementContainedInCanonical =
  Future.anyCongruentRefinementIsContainedInFutureEquivalent

------------------------------------------------------------------------
-- 2. A residual safe for the canonical future relation.
------------------------------------------------------------------------

record FutureSafeResidual
    {State Action Observation Residual : Set}
    (system : Dependency.DependentActionSystem State Action)
    (project : State -> Observation)
    (residual : State -> Residual) : Set₁ where
  constructor future-safe-residual
  field
    safePair :
      Lower.DynamicallySufficientPair
        State
        Observation
        Residual
        (CanonicalFutureRelation system project)
        project
        residual

open FutureSafeResidual public

futureSafeResidualSeparatesFutureDistinctPair :
  ∀ {State Action Observation Residual}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {residual : State -> Residual} ->
  FutureSafeResidual system project residual ->
  {left right : State} ->
  project left ≡ project right ->
  (CanonicalFutureRelation system project left right -> ⊥) ->
  residual left ≡ residual right ->
  ⊥
futureSafeResidualSeparatesFutureDistinctPair safe coarseSame futureDistinct =
  Lower.distinctFutureClassesForceDistinctResiduals
    (safePair safe)
    coarseSame
    futureDistinct

------------------------------------------------------------------------
-- 3. Finite class-capacity theorem over the canonical future relation.
------------------------------------------------------------------------

CanonicalFiniteFutureDistinctFibre :
  ∀ {State Action Observation : Set} ->
  (k : Nat) ->
  (system : Dependency.DependentActionSystem State Action) ->
  (project : State -> Observation) ->
  Set₁
CanonicalFiniteFutureDistinctFibre k system project =
  Cardinality.FiniteFutureDistinctFibre
    k
    (CanonicalFutureRelation system project)
    project

futureSafeResidualInjectsCanonicalFutureClasses :
  ∀ {State Action Observation Residual k}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {residual : State -> Residual} ->
  FutureSafeResidual system project residual ->
  (fibre : CanonicalFiniteFutureDistinctFibre k system project) ->
  Cardinality.Injective
    (λ index ->
      residual (Cardinality.representative fibre index))
futureSafeResidualInjectsCanonicalFutureClasses safe fibre =
  Cardinality.residualInjectionFromFutureDistinctFibre
    (safePair safe)
    fibre

futureSafeBitResidualCapacityBound :
  ∀ {State Action Observation k bits}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {residual : State -> Cardinality.BitWords bits} ->
  FutureSafeResidual system project residual ->
  (fibre : CanonicalFiniteFutureDistinctFibre k system project) ->
  k ≤ Cardinality.pow2 bits
futureSafeBitResidualCapacityBound safe fibre =
  Cardinality.futureSafetyForBitWordsImpliesCapacityBound
    (safePair safe)
    fibre

futureSafeBitResidualRespectsCertifiedMinimum :
  ∀ {State Action Observation k bits minimumBits}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    {residual : State -> Cardinality.BitWords bits} ->
  Cardinality.CeilLog2Certificate k minimumBits ->
  FutureSafeResidual system project residual ->
  (fibre : CanonicalFiniteFutureDistinctFibre k system project) ->
  minimumBits ≤ bits
futureSafeBitResidualRespectsCertifiedMinimum certificate safe fibre =
  Cardinality.safeBitResidualRespectsCeilLog2
    certificate
    (safePair safe)
    fibre

------------------------------------------------------------------------
-- 4. Exact interpretation boundary.
------------------------------------------------------------------------

record FutureSafeCoarseFibreCapacityBoundary : Set where
  constructor future-safe-coarse-fibre-capacity-boundary
  field
    canonicalRelationIsFutureEquivalent : Bool
    canonicalRelationIsCoarsestDynamicallySafeRefinement : Bool
    futureDistinctClassesRequireDistinctSafeResidualCodes : Bool
    finiteFutureDistinctClassCountGivesCapacityLowerBound : Bool
    everyCurrentDifferenceMustBeRetained : Bool
    everyCurrentDifferenceMustBeRetainedIsFalse :
      everyCurrentDifferenceMustBeRetained ≡ false
    everyFineDifferenceMustBeRetained : Bool
    everyFineDifferenceMustBeRetainedIsFalse :
      everyFineDifferenceMustBeRetained ≡ false
    futureSafetyCreatesDomainMechanism : Bool
    futureSafetyCreatesDomainMechanismIsFalse :
      futureSafetyCreatesDomainMechanism ≡ false

canonicalFutureSafeCoarseFibreCapacityBoundary :
  FutureSafeCoarseFibreCapacityBoundary
canonicalFutureSafeCoarseFibreCapacityBoundary =
  future-safe-coarse-fibre-capacity-boundary
    true true true true
    false refl
    false refl
    false refl
