module DASHI.Mathematics.Complexity.PNotEqualsNPQ1StagedRootedSourceConstructorExact where

------------------------------------------------------------------------
-- STAGED ROOTED SOURCE CONSTRUCTOR WITH EXPLICIT STOP REASON
--
-- B0 identified a defect in the live DirectDP constructor interface:
--
--   state -> Maybe run
--
-- permits an opaque always-stop implementation. The rooted source machinery
-- already has a deterministic construction and one real gate: declared work
-- must fit strictly inside the supplied budget.
--
-- This owner exposes that gate as a TOTAL staged result:
--
--   sourceReady exact-output fit
--   budgetExhausted budget<=declared-work
--
-- Thus `nothing` is eliminated at the source-construction layer. The next
-- compiler may fail only for an additional EXPLICIT reason that it introduces.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact as Completed

------------------------------------------------------------------------
-- Total result type.
------------------------------------------------------------------------

data RootedSourceStage
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) : Set₁ where

  sourceReady :
    (terminalKeys : List (Merge.SemanticKey zero)) →
    terminalKeys
      ≡ Root.rootedMergedSemanticKeys
          (Completed.completeRootDescent root) →
    Completed.completedRootedSourceWork root < budget →
    RootedSourceStage root budget

  budgetExhausted :
    budget ≤ Completed.completedRootedSourceWork root →
    RootedSourceStage root budget

------------------------------------------------------------------------
-- Deterministic staged constructor.
------------------------------------------------------------------------

stagedRootedSource :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) →
  RootedSourceStage root budget
stagedRootedSource root budget
    with NatP._<?_
      (Completed.completedRootedSourceWork root)
      budget
... | yes fits =
  sourceReady
    (Root.rootedMergedSemanticKeys
      (Completed.completeRootDescent root))
    refl
    fits
... | no doesNotFit =
  budgetExhausted
    (NatP.≮⇒≥ doesNotFit)

------------------------------------------------------------------------
-- Projection recovers the previous Maybe gate exactly.
------------------------------------------------------------------------

stageToMaybe :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  RootedSourceStage root budget →
  Maybe
    (Σ
      (List (Merge.SemanticKey zero))
      (λ terminalKeys →
        (terminalKeys
          ≡ Root.rootedMergedSemanticKeys
              (Completed.completeRootDescent root))
        ×
        (Completed.completedRootedSourceWork root < budget)))
stageToMaybe (sourceReady terminalKeys exact fits) =
  just (terminalKeys , (exact , fits))
stageToMaybe (budgetExhausted exhausted) =
  nothing

stagedRootedSourceProjectsToOldGate :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) →
  stageToMaybe (stagedRootedSource root budget)
  ≡
  Completed.completedRootedSourceGate root budget
stagedRootedSourceProjectsToOldGate root budget
    with NatP._<?_
      (Completed.completedRootedSourceWork root)
      budget
... | yes fits = refl
... | no doesNotFit = refl

------------------------------------------------------------------------
-- Exhaustion and success are disjoint by arithmetic, independent of syntax.
------------------------------------------------------------------------

sourceFitAndExhaustionContradict :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  Completed.completedRootedSourceWork root < budget →
  budget ≤ Completed.completedRootedSourceWork root →
  ⊥
sourceFitAndExhaustionContradict fits exhausted =
  NatP.<⇒≱ fits exhausted

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The rooted exhaustive source stage no longer has an opaque stop. Its only
-- failure reason is budget exhaustion.
--
-- Still missing for a live DirectDP run:
--   rooted source data -> one flat TransitionTableCandidate
--   + finite semantic admission
--   + a typed machine trace paying for that exact compilation/evaluation.
------------------------------------------------------------------------
