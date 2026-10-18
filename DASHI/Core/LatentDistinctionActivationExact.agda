module DASHI.Core.LatentDistinctionActivationExact where

------------------------------------------------------------------------
-- LATENT DISTINCTION ACTIVATION
--
-- Canonical dynamic shape:
--
--   project left = project right
--   left  -- common admissible trace --> leftAfter
--   right -- common admissible trace --> rightAfter
--   project leftAfter /= project rightAfter
--
-- This is exactly DynamicalQuotientSafety.TerminalisationDefect.  The present
-- module does not duplicate that record; it packages the consequences needed by
-- the future-refinement / residual-capacity lanes:
--
--   * the pair is not FutureEquivalent;
--   * a future-safe residual must separate the pair;
--   * any two-state finite future-distinct fibre therefore requires capacity
--     for at least two residual codes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as Capacity
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality

LatentDistinctionActivation :
  ∀ {State Action Observation : Set} ->
  Dependency.DependentActionSystem State Action ->
  (State -> Observation) ->
  Set₁
LatentDistinctionActivation system project =
  Dynamic.TerminalisationDefect system project

-- Explicit form with readable arguments; this is the preferred consumer API.
activationPairNotFutureEquivalent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project) ->
  Future.FutureEquivalent
    system project
    (Dynamic.left activation)
    (Dynamic.right activation) ->
  ⊥
activationPairNotFutureEquivalent activation future =
  Dynamic.futureObservationsDiffer activation
    (future
      (Dynamic.leftExecution activation)
      (Dynamic.rightExecution activation))

activationReversePairNotFutureEquivalent :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project) ->
  Future.FutureEquivalent
    system project
    (Dynamic.right activation)
    (Dynamic.left activation) ->
  ⊥
activationReversePairNotFutureEquivalent activation future =
  Dynamic.futureObservationsDiffer activation
    (sym
      (future
        (Dynamic.rightExecution activation)
        (Dynamic.leftExecution activation)))

activationRepresentative :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation} ->
  LatentDistinctionActivation system project ->
  Fin 2 ->
  State
activationRepresentative activation zero = Dynamic.left activation
activationRepresentative activation (suc zero) = Dynamic.right activation

activationFutureEquivalentIndicesEqual :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project)
    {leftIndex rightIndex : Fin 2} ->
  Future.FutureEquivalent
    system
    project
    (activationRepresentative activation leftIndex)
    (activationRepresentative activation rightIndex) ->
  leftIndex ≡ rightIndex
activationFutureEquivalentIndicesEqual activation {zero} {zero} future = refl
activationFutureEquivalentIndicesEqual activation {zero} {suc zero} future =
  ⊥-elim (activationPairNotFutureEquivalent activation future)
activationFutureEquivalentIndicesEqual activation {suc zero} {zero} future =
  ⊥-elim (activationReversePairNotFutureEquivalent activation future)
activationFutureEquivalentIndicesEqual activation {suc zero} {suc zero} future = refl

activationTwoClassFutureDistinctFibre :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project) ->
  Capacity.CanonicalFiniteFutureDistinctFibre
    2
    system
    project
activationTwoClassFutureDistinctFibre activation =
  Cardinality.finiteFutureDistinctFibre
    (activationRepresentative activation)
    (project (Dynamic.left activation))
    (λ
      { zero -> refl
      ; (suc zero) -> sym (Dynamic.sameCurrentObservation activation)
      })
    (activationFutureEquivalentIndicesEqual activation)

activationForcesResidualInjection :
  ∀ {State Action Observation Residual}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project)
    {residual : State -> Residual} ->
  Capacity.FutureSafeResidual system project residual ->
  Cardinality.Injective
    (λ index ->
      residual (activationRepresentative activation index))
activationForcesResidualInjection activation safe =
  Capacity.futureSafeResidualInjectsCanonicalFutureClasses
    safe
    (activationTwoClassFutureDistinctFibre activation)

activationForcesBitCapacity :
  ∀ {State Action Observation bits}
    {system : Dependency.DependentActionSystem State Action}
    {project : State -> Observation}
    (activation : LatentDistinctionActivation system project)
    {residual : State -> Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual system project residual ->
  2 ≤ Cardinality.pow2 bits
activationForcesBitCapacity activation safe =
  Capacity.futureSafeBitResidualCapacityBound
    safe
    (activationTwoClassFutureDistinctFibre activation)

record LatentDistinctionActivationBoundary : Set where
  constructor latent-distinction-activation-boundary
  field
    terminalisationDefectReused : Bool
    futureEquivalentRefutationDerived : Bool
    twoClassResidualCapacityDerived : Bool
    hiddenDifferenceAutomaticallyMatters : Bool
    hiddenDifferenceAutomaticallyMattersIsFalse :
      hiddenDifferenceAutomaticallyMatters ≡ false
    commonAdmissibleTraceRequired : Bool
    laterObservationSeparationRequired : Bool
    theoremCreatesDomainMechanism : Bool
    theoremCreatesDomainMechanismIsFalse :
      theoremCreatesDomainMechanism ≡ false

canonicalLatentDistinctionActivationBoundary :
  LatentDistinctionActivationBoundary
canonicalLatentDistinctionActivationBoundary =
  latent-distinction-activation-boundary
    true true true
    false refl
    true true
    false refl
