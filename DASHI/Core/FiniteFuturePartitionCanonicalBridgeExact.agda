module DASHI.Core.FiniteFuturePartitionCanonicalBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FiniteFuturePartitionRefinementExact as Partition
import DASHI.Core.FutureEquivalenceCurrentObservationExact as Current
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- CANONICAL BRIDGE FOR THE COMPUTED FINITE QUOTIENT
------------------------------------------------------------------------

record ExactStepPost
    (before : Partition.State)
    (action : Partition.Action)
    (after : Partition.State) : Set where
  constructor exactStepPost
  field
    afterIsStep : after ≡ Partition.step action before

open ExactStepPost public

partitionSystem :
  Dependency.DependentActionSystem Partition.State Partition.Action
partitionSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = ExactStepPost
  ; actionLabel = λ action → "partition advance"
  }

canonicalAdmissible :
  (state : Partition.State) →
  (action : Partition.Action) →
  Dependency.AdmissibleAction partitionSystem state action
canonicalAdmissible state action = record
  { precondition = tt
  ; after = Partition.step action state
  ; postcondition = exactStepPost refl
  ; dependencyReceipt = "deterministic partition-refinement step"
  }

canonicalExecutes :
  (actions : List Partition.Action) →
  (state : Partition.State) →
  Reachability.Executes
    partitionSystem actions state (Partition.run actions state)
canonicalExecutes [] state = Reachability.executesNil
canonicalExecutes (action ∷ rest) state =
  Reachability.executesCons
    (canonicalAdmissible state action)
    (canonicalExecutes rest (Partition.step action state))

executionTargetIsRun :
  ∀ {actions before after} →
  Reachability.Executes partitionSystem actions before after →
  after ≡ Partition.run actions before
executionTargetIsRun Reachability.executesNil = refl
executionTargetIsRun
  (Reachability.executesCons admissible rest)
  with afterIsStep (Dependency.postcondition admissible)
... | refl = executionTargetIsRun rest

------------------------------------------------------------------------
-- Stable refined-code equality implies canonical future equivalence.
------------------------------------------------------------------------

stableCodeEqualityImpliesCanonicalFutureEquivalent :
  {left right : Partition.State} →
  Partition.refineCode left ≡ Partition.refineCode right →
  Future.FutureObservationEquivalent
    partitionSystem Partition.observe left right
stableCodeEqualityImpliesCanonicalFutureEquivalent {left} {right} codeEqual =
  Future.futureObservationEquivalent λ actions observation →
    Future.logicalIff (forwardWitness actions observation) (backwardWitness actions observation)
  where
    traceObservationEqual :
      (actions : List Partition.Action) →
      Partition.observe (Partition.run actions left)
      ≡ Partition.observe (Partition.run actions right)
    traceObservationEqual =
      Partition.stableRefinementIsFutureSafe codeEqual

    forwardWitness :
      (actions : List Partition.Action) →
      (observation : Bool) →
      Future.FutureObservation partitionSystem Partition.observe left actions observation →
      Future.FutureObservation partitionSystem Partition.observe right actions observation
    forwardWitness actions observation
      (Future.futureObservation after execution observationProof)
      with executionTargetIsRun execution
    ... | refl =
      Future.futureObservation
        (Partition.run actions right)
        (canonicalExecutes actions right)
        (trans (sym (traceObservationEqual actions)) observationProof)

    backwardWitness :
      (actions : List Partition.Action) →
      (observation : Bool) →
      Future.FutureObservation partitionSystem Partition.observe right actions observation →
      Future.FutureObservation partitionSystem Partition.observe left actions observation
    backwardWitness actions observation
      (Future.futureObservation after execution observationProof)
      with executionTargetIsRun execution
    ... | refl =
      Future.futureObservation
        (Partition.run actions left)
        (canonicalExecutes actions left)
        (trans (traceObservationEqual actions) observationProof)

------------------------------------------------------------------------
-- Conversely, canonical future equivalence determines both fields of the
-- one-step refined code: present observation by the empty trace, and next
-- observation by the singleton `advance` trace.
------------------------------------------------------------------------

futureEquivalentImpliesNextObservationEqual :
  {left right : Partition.State} →
  Future.FutureObservationEquivalent
    partitionSystem Partition.observe left right →
  Partition.observe (Partition.step Partition.advance left)
  ≡ Partition.observe (Partition.step Partition.advance right)
futureEquivalentImpliesNextObservationEqual {left} {right} equivalent
  with Future.forward
    (Future.sameFutureLanguage equivalent
      (Partition.advance ∷ [])
      (Partition.observe (Partition.step Partition.advance left)))
    leftNextWitness
  where
    leftNextWitness :
      Future.FutureObservation
        partitionSystem Partition.observe left
        (Partition.advance ∷ [])
        (Partition.observe (Partition.step Partition.advance left))
    leftNextWitness =
      Future.futureObservation
        (Partition.step Partition.advance left)
        (canonicalExecutes (Partition.advance ∷ []) left)
        refl
... | Future.futureObservation after execution observationProof
  with executionTargetIsRun execution
... | refl = sym observationProof

refinedCodeCongruence :
  ∀ {left right : Partition.State} →
  Partition.observe left ≡ Partition.observe right →
  Partition.observe (Partition.step Partition.advance left)
    ≡ Partition.observe (Partition.step Partition.advance right) →
  Partition.refineCode left ≡ Partition.refineCode right
refinedCodeCongruence refl refl = refl

canonicalFutureEquivalentImpliesStableCodeEquality :
  {left right : Partition.State} →
  Future.FutureObservationEquivalent
    partitionSystem Partition.observe left right →
  Partition.refineCode left ≡ Partition.refineCode right
canonicalFutureEquivalentImpliesStableCodeEquality equivalent =
  refinedCodeCongruence
    (Current.futureEquivalentImpliesCurrentObservationEqual equivalent)
    (futureEquivalentImpliesNextObservationEqual equivalent)

------------------------------------------------------------------------
-- The computed stable code is therefore an exact presentation of the
-- repository's canonical future-equivalence quotient for this machine.
------------------------------------------------------------------------

stableRefinementPresentation :
  Future.FutureEquivalencePresentation partitionSystem Partition.observe
stableRefinementPresentation =
  Future.futureEquivalencePresentation
    Partition.RefinedCode
    Partition.refineCode
    stableCodeEqualityImpliesCanonicalFutureEquivalent
    canonicalFutureEquivalentImpliesStableCodeEquality
