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
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (_≤_; _<_)
open import Data.Product using (Σ; _×_; _,_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact as Completed

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

sourceExhaustionImpliesCompletedGateFailure :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  budget ≤ Completed.completedRootedSourceWork root →
  Completed.completedRootedSourceGate root budget
  ≡
  nothing
sourceExhaustionImpliesCompletedGateFailure
    {root = root}
    {budget = budget}
    exhausted =
  Completed.completedRootedSourceFailsOnExhaustion
    root
    budget
    exhausted

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
-- Stage 1 is total and same-object:
--   work < budget  -> exact sourceReady
--   budget <= work -> exact sourceWorkExhausted.
--
-- Success does NOT yet promote to a DirectDP/Q1 run; packing,
-- verifier-backed admission, concrete machine execution and the final charged
-- inequality remain explicit subsequent stages.
------------------------------------------------------------------------
