module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExhaustiveEnumerationCostObstructionExact where

------------------------------------------------------------------------
-- CONCRETE COST OBSTRUCTION TO THE *EXHAUSTIVE* SHANNON COMPILER
--
-- The root-generated reference builder expands every raw Shannon history
-- BEFORE canonical semantic-key merging. Thus its declared last-layer work
-- is at least the number of raw children emitted from the previous layer,
-- independently of how few semantic classes remain after merging.
--
-- This is an unconditional statement about THIS constructor. It is NOT a
-- lower bound on arbitrary canonical automaton builders, SAT algorithms, or
-- the Clay P!=NP question.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Maybe using (nothing)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1EnumeratedMergedLayerExact as Step
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateFailureExact as Failure

------------------------------------------------------------------------
-- The last raw layer is doubled, regardless of semantic-key collisions.
------------------------------------------------------------------------

rawChildCountExact :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining)) →
  Root.rootedLayerEnumerationCount (Root.descend previous)
  ≡
  Step.oneLayerEnumerationWork (Root.rootedLayer previous)
rawChildCountExact previous =
  Root.rootedLayerCountAfterDescent previous

------------------------------------------------------------------------
-- One last-layer expansion cost is always present in declared ROOT work.
------------------------------------------------------------------------

lastExpansionBelowRootedDeclaredWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining)) →
  Step.oneLayerEnumerationWork (Root.rootedLayer previous)
  ≤
  Root.rootedDeclaredWork (Root.descend previous)
lastExpansionBelowRootedDeclaredWork previous =
  NatP.≤-trans
    (NatP.m≤m+n
      (Step.oneLayerEnumerationWork (Root.rootedLayer previous))
      (Step.oneLayerKeyWork (Root.rootedLayer previous)))
    (NatP.m≤n+m
      (Step.oneLayerDeclaredWork (Root.rootedLayer previous))
      (Root.rootedDeclaredWork previous))

------------------------------------------------------------------------
-- That cost remains in the new combined source-work gate as well.
------------------------------------------------------------------------

lastExpansionBelowOperationalWork :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining)) →
  Step.oneLayerEnumerationWork (Root.rootedLayer previous)
  ≤
  Work.rootedDeclaredOperationalWork (Root.descend previous)
lastExpansionBelowOperationalWork previous =
  NatP.≤-trans
    (lastExpansionBelowRootedDeclaredWork previous)
    (NatP.≤-trans
      (NatP.m≤m+n
        (Root.rootedDeclaredWork (Root.descend previous))
        (Work.rootedAllLayerEvaluationWork (Root.descend previous)))
      (NatP.m≤m+n
        (Root.rootedDeclaredWork (Root.descend previous)
          +
         Work.rootedAllLayerEvaluationWork (Root.descend previous))
        (Work.rootedAllLayerTransitionWork (Root.descend previous))))

------------------------------------------------------------------------
-- Thus a strict budget not exceeding the latest raw expansion cannot
-- admit this particular exhaustive constructor, even if merging collapses
-- all those raw histories into a small quotient.
------------------------------------------------------------------------

smallBudgetForcesExhaustiveFailure :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining))
    (budget : Nat) →
  budget
    ≤ Step.oneLayerEnumerationWork (Root.rootedLayer previous) →
  Work.budgetedRootedKeys (Root.descend previous) budget
    ≡
    nothing
smallBudgetForcesExhaustiveFailure previous budget small =
  Failure.rootedWorkGateFailsIfWorkExhaustsBudget
    (Root.descend previous)
    budget
    (NatP.≤-trans
      small
      (lastExpansionBelowOperationalWork previous))

------------------------------------------------------------------------
-- No transfer to a GENERATIVE quotient algorithm has occurred: one may
-- merge/recursively update a compact repair state before enumerating all
-- raw restrictions. That is precisely the still-open B1 research path.
------------------------------------------------------------------------
