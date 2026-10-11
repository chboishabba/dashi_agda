module DASHI.Mathematics.Complexity.PNotEqualsNPQ1StagedRootedSourceConstructorExact where

------------------------------------------------------------------------
-- STAGED ROOTED SOURCE CONSTRUCTOR WITH EXPLICIT STOP REASON
--
-- B0 identified a defect in the live DirectDP constructor interface:
--
--   state -> Maybe run
--
-- permits an opaque always-stop implementation.  The rooted source machinery
-- already has a deterministic construction and one real gate: declared work
-- must fit strictly inside the supplied budget.
--
-- This owner exposes that gate as a TOTAL staged result:
--
--   sourceReady exact-output fit
--   budgetExhausted budget<=declared-work
--
-- Thus `nothing` is eliminated at the source-construction layer.  The next
-- compiler may fail only for an additional EXPLICIT reason that it introduces.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
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
-- Exact agreement with the old Maybe gate.
------------------------------------------------------------------------

sourceReadyGivesGateSuccess :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat)
    {terminalKeys : List (Merge.SemanticKey zero)}
    {exact :
      terminalKeys
      ≡ Root.rootedMergedSemanticKeys
          (Completed.completeRootDescent root)}
    {fits : Completed.completedRootedSourceWork root < budget} →
  stagedRootedSource root budget
  ≡ sourceReady terminalKeys exact fits →
  Completed.completedRootedSourceGate root budget
  ≡
  just
    (Root.rootedMergedSemanticKeys
      (Completed.completeRootDescent root)
    ,
    (refl , fits))
sourceReadyGivesGateSuccess root budget equality
    with NatP._<?_
      (Completed.completedRootedSourceWork root)
      budget
... | yes actualFits =
  refl
... | no doesNotFit =
  impossible equality
  where
    impossible :
      budgetExhausted
        (NatP.≮⇒≥ doesNotFit)
      ≡ sourceReady _ _ _ →
      Completed.completedRootedSourceGate root budget
      ≡ just
          (Root.rootedMergedSemanticKeys
            (Completed.completeRootDescent root)
          ,
          (refl , fits))
    impossible ()

budgetExhaustedGivesGateFailure :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat)
    {exhausted : budget ≤ Completed.completedRootedSourceWork root} →
  stagedRootedSource root budget
  ≡ budgetExhausted exhausted →
  Completed.completedRootedSourceGate root budget
  ≡ nothing
budgetExhaustedGivesGateFailure root budget equality =
  Completed.completedRootedSourceFailsOnExhaustion
    root
    budget
    exhausted

------------------------------------------------------------------------
-- Exhaustion and success are disjoint by arithmetic, independent of syntax.
------------------------------------------------------------------------

sourceFitAndExhaustionContradict :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {budget : Nat} →
  Completed.completedRootedSourceWork root < budget →
  budget ≤ Completed.completedRootedSourceWork root →
  Data.Empty.⊥
sourceFitAndExhaustionContradict fits exhausted =
  NatP.<⇒≱ fits exhausted

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The rooted exhaustive source stage no longer has an opaque stop.  Its only
-- failure reason is budget exhaustion.
--
-- Still missing for a live DirectDP run:
--   rooted source data -> one flat TransitionTableCandidate
--   + finite semantic admission
--   + a typed machine trace paying for that exact compilation/evaluation.
------------------------------------------------------------------------
