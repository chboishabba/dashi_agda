module DASHI.Mathematics.Complexity.PNotEqualsNPQ1StagedRootedConstructorExact where

------------------------------------------------------------------------
-- STAGED ROOTED Q1 CONSTRUCTOR STATUS
--
-- Replaces an opaque Maybe stop at the SOURCE-CONSTRUCTION boundary with a
-- total, inspectable result.
--
-- Stage 1 is fully implemented:
--   compute the exact full-depth rooted source work;
--   if it strictly fits the requested budget, return the SAME canonical
--   zero-arity rooted key list with the strict-work receipt;
--   otherwise return an explicit sourceWorkExhausted proof.
--
-- Later stages (global packing, verifier-backed admission, concrete emitting
-- machine and full charged fit) remain separate typed stop reasons rather than
-- being silently collapsed to nothing.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact as Completed

------------------------------------------------------------------------
-- Same-object source success payload.
------------------------------------------------------------------------

record RootedSourceReady
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) : Set where
  constructor rooted-source-ready
  field
    terminalKeys : List (Merge.SemanticKey zero)

    terminalKeysExact :
      terminalKeys
      ≡
      Root.rootedMergedSemanticKeys
        (Completed.completeRootDescent root)

    sourceWorkFits :
      Completed.completedRootedSourceWork root
      <
      budget

open RootedSourceReady public

------------------------------------------------------------------------
-- Explicit source-stage result.
------------------------------------------------------------------------

data RootedSourceStageResult
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) : Set where

  sourceWorkExhausted :
    budget ≤ Completed.completedRootedSourceWork root →
    RootedSourceStageResult root budget

  sourceReady :
    RootedSourceReady root budget →
    RootedSourceStageResult root budget

runRootedSourceStage :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) →
  RootedSourceStageResult root budget
runRootedSourceStage root budget
    with NatP._<?_
      (Completed.completedRootedSourceWork root)
      budget
... | yes fits =
  sourceReady
    (rooted-source-ready
      (Root.rootedMergedSemanticKeys
        (Completed.completeRootDescent root))
      refl
      fits)
... | no doesNotFit =
  sourceWorkExhausted
    (NatP.≮⇒≥ doesNotFit)

------------------------------------------------------------------------
-- Exhaustive characterization of Stage 1.
------------------------------------------------------------------------

sourceReadyImpliesCompletedGateSuccess :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  RootedSourceReady root budget →
  Σ
    (List (Merge.SemanticKey zero))
    (λ terminalKeys →
      (terminalKeys
        ≡ Root.rootedMergedSemanticKeys
          (Completed.completeRootDescent root))
      ×
      (Completed.completedRootedSourceWork root < budget))
sourceReadyImpliesCompletedGateSuccess ready =
  terminalKeys ready
  ,
  (terminalKeysExact ready , sourceWorkFits ready)
  where
    open import Data.Product using (Σ; _×_; _,_)

sourceExhaustionImpliesCompletedGateFailure :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  budget ≤ Completed.completedRootedSourceWork root →
  Completed.completedRootedSourceGate root budget
  ≡
  Data.Maybe.Base.nothing
sourceExhaustionImpliesCompletedGateFailure exhausted =
  Completed.completedRootedSourceFailsOnExhaustion
    _
    _
    exhausted

------------------------------------------------------------------------
-- The rest of the constructor is now an explicit staged frontier.
------------------------------------------------------------------------

data PostSourceStopReason : Set where
  packedTransitionCandidateMissing : PostSourceStopReason
  verifierBackedAdmissionMissing : PostSourceStopReason
  emittingMachineReceiptMissing : PostSourceStopReason
  fullChargedStrictFitMissing : PostSourceStopReason

record PostSourceFrontier
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) : Set where
  constructor post-source-frontier
  field
    source : RootedSourceReady root budget
    nextStop : PostSourceStopReason

------------------------------------------------------------------------
-- MAX-CUT INTERPRETATION
--
-- The old arbitrary constructor could simply return nothing with no reason.
-- At the rooted source stage that opacity is gone:
--
--   work < budget  -> exact sourceReady
--   budget <= work -> exact sourceWorkExhausted
--
-- Therefore any future first-step progress proof has a concrete first branch
-- to eliminate.  Success does NOT yet promote to a DirectDP/Q1 run; packing,
-- verifier-backed admission, concrete machine execution and the final charged
-- inequality remain explicit subsequent stages.
------------------------------------------------------------------------
