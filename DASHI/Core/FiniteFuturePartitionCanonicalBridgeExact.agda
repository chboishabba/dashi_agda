module DASHI.Core.FiniteFuturePartitionCanonicalBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FiniteFuturePartitionRefinementExact as Partition
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- CANONICAL BRIDGE FOR THE COMPUTED FINITE QUOTIENT
--
-- FiniteFuturePartitionRefinementExact computes a stable deterministic code.
-- This module proves that code is safe for the repository's canonical,
-- proof-bearing future-observation relation rather than only for a parallel
-- custom trace semantics.
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
-- Every stable-code equality is a canonical future-observation equivalence.
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
-- A concrete future-equivalence presentation can therefore use the stable
-- refined code directly as its quotient code.
------------------------------------------------------------------------

stableRefinementPresentation :
  Future.FutureEquivalencePresentation partitionSystem Partition.observe
stableRefinementPresentation =
  Future.futureEquivalencePresentation
    Partition.RefinedCode
    Partition.refineCode
    stableCodeEqualityImpliesCanonicalFutureEquivalent
    complete
  where
    complete :
      ∀ {left right} →
      Future.FutureObservationEquivalent
        partitionSystem Partition.observe left right →
      Partition.refineCode left ≡ Partition.refineCode right
    complete {Partition.source} {Partition.source} equivalent = refl
    complete {Partition.source} {Partition.memo} equivalent =
      ⊥-elim (sourceMemoContradiction equivalent)
    complete {Partition.source} {Partition.twin} equivalent =
      ⊥-elim (sourceTwinContradiction equivalent)
    complete {Partition.source} {Partition.accepting} equivalent =
      ⊥-elim (currentContradiction equivalent)
    complete {Partition.memo} {Partition.source} equivalent =
      ⊥-elim (sourceMemoContradiction (Future.futureEquivalentSym equivalent))
    complete {Partition.memo} {Partition.memo} equivalent = refl
    complete {Partition.memo} {Partition.twin} equivalent = refl
    complete {Partition.memo} {Partition.accepting} equivalent =
      ⊥-elim (currentContradiction equivalent)
    complete {Partition.twin} {Partition.source} equivalent =
      ⊥-elim (sourceTwinContradiction (Future.futureEquivalentSym equivalent))
    complete {Partition.twin} {Partition.memo} equivalent = refl
    complete {Partition.twin} {Partition.twin} equivalent = refl
    complete {Partition.twin} {Partition.accepting} equivalent =
      ⊥-elim (currentContradiction equivalent)
    complete {Partition.accepting} {Partition.source} equivalent =
      ⊥-elim (currentContradiction (Future.futureEquivalentSym equivalent))
    complete {Partition.accepting} {Partition.memo} equivalent =
      ⊥-elim (currentContradiction (Future.futureEquivalentSym equivalent))
    complete {Partition.accepting} {Partition.twin} equivalent =
      ⊥-elim (currentContradiction (Future.futureEquivalentSym equivalent))
    complete {Partition.accepting} {Partition.accepting} equivalent = refl

    currentContradiction :
      ∀ {left right} →
      Future.FutureObservationEquivalent partitionSystem Partition.observe left right →
      Partition.observe left ≡ Partition.observe right → ⊥
    currentContradiction equivalent impossible = impossible impossible

    sourceMemoContradiction :
      Future.FutureObservationEquivalent
        partitionSystem Partition.observe Partition.source Partition.memo → ⊥
    sourceMemoContradiction equivalent =
      impossible
        (Future.forward
          (Future.sameFutureLanguage equivalent
            (Partition.advance ∷ []) true)
          sourceReachesTrue)
      where
        sourceReachesTrue :
          Future.FutureObservation
            partitionSystem Partition.observe Partition.source
            (Partition.advance ∷ []) true
        sourceReachesTrue =
          Future.futureObservation
            Partition.accepting
            (canonicalExecutes (Partition.advance ∷ []) Partition.source)
            refl

        impossible :
          Future.FutureObservation
            partitionSystem Partition.observe Partition.memo
            (Partition.advance ∷ []) true → ⊥
        impossible
          (Future.futureObservation after execution observationProof)
          with executionTargetIsRun execution
        ... | refl = falseTrueImpossible observationProof
          where
            falseTrueImpossible : false ≡ true → ⊥
            falseTrueImpossible ()

    sourceTwinContradiction :
      Future.FutureObservationEquivalent
        partitionSystem Partition.observe Partition.source Partition.twin → ⊥
    sourceTwinContradiction equivalent =
      sourceMemoContradiction
        (Future.futureEquivalentTrans equivalent
          (stableCodeEqualityImpliesCanonicalFutureEquivalent refl))
