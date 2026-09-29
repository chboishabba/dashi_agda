module DASHI.Mathematics.Complexity.PNotEqualsNPQ1CompletedRootedSourceGateExact where

------------------------------------------------------------------------
-- FULL-DEPTH ROOT-REACHABLE QUOTIENT: DECLARED OUTPUT + WORK GATE
--
-- Unlike the earlier arbitrary-layer rooted work gate, this owner computes
-- a unique terminal path by repeatedly restricting until arity zero.
--
-- Its source output contains:
--   * actual canonical root-reachable keys at every generated layer;
--   * exactly two emitted edge rows per indexed nonterminal state;
--   * the literal terminal-observation rows at the final zero-arity layer.
--
-- The declared charge combines the existing enumeration/evaluation/lookup
-- work with the actual emitted output-cell lengths.
--
-- This remains a high-level work ledger, NOT a concrete tape-machine trace,
-- nor an inhabitant of the charged DirectDP constructor. It is permitted to
-- return nothing for budget exhaustion at the candidate's own Q2 measure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalTruthTableMergeExact as Merge
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableEdgeTableExact as Rows
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedWorkGateExact as Work

------------------------------------------------------------------------
-- The terminal path is itself computed from the literal root and the
-- variable count, without a supplied finite-state graph.
------------------------------------------------------------------------

descendToTerminal :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Root.DescentPath root remaining →
  Root.DescentPath root zero
descendToTerminal {remaining = zero} path =
  path
descendToTerminal {remaining = suc remaining} path =
  descendToTerminal (Root.descend path)

completeRootDescent :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Root.DescentPath root zero
completeRootDescent root =
  descendToTerminal Root.atRoot

------------------------------------------------------------------------
-- Actually emitted graph cells: one per canonical key, two per edge source,
-- and one per terminal label. All counts are taken from COMPUTED lists.
------------------------------------------------------------------------

rootedStateAndEdgeCells :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  (path : Root.DescentPath root remaining) →
  Nat
rootedStateAndEdgeCells Root.atRoot =
  length (Root.rootedMergedSemanticKeys Root.atRoot)
rootedStateAndEdgeCells (Root.descend previous) =
  rootedStateAndEdgeCells previous
  + length (Root.rootedMergedSemanticKeys (Root.descend previous))
  + (length (Rows.allReachableEdgeRows previous)
     + length (Rows.allReachableEdgeRows previous))

completedTerminalLabelCells :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Nat
completedTerminalLabelCells root =
  length
    (Rows.allReachableTerminalRows
      (completeRootDescent root))

completedRootedSourceWork :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) →
  Nat
completedRootedSourceWork root =
  Work.rootedDeclaredOperationalWork (completeRootDescent root)
  +
  rootedStateAndEdgeCells (completeRootDescent root)
  +
  completedTerminalLabelCells root

------------------------------------------------------------------------
-- A strict gate on the full root-to-terminal construction. Output identity
-- is part of the SUCCESS TYPE: arbitrary unrelated key lists are excluded.
------------------------------------------------------------------------

completedRootedSourceGate :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) →
  Maybe
    (Σ
      (List (Merge.SemanticKey zero))
      (λ terminalKeys →
        (terminalKeys
          ≡ Root.rootedMergedSemanticKeys (completeRootDescent root))
        ×
        (completedRootedSourceWork root < budget)))
completedRootedSourceGate root budget
    with NatP._<?_
      (completedRootedSourceWork root)
      budget
... | yes fits =
  just (Root.rootedMergedSemanticKeys (completeRootDescent root) ,
    (refl , fits))
... | no doesNotFit =
  nothing

------------------------------------------------------------------------
-- Deliberately no all-input success theorem: failure follows whenever the
-- full declared source work itself exhausts the requested budget.
------------------------------------------------------------------------

completedRootedSourceFailsOnExhaustion :
  ∀ {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables)
    (budget : Nat) →
  budget ≤ completedRootedSourceWork root →
  completedRootedSourceGate root budget ≡ nothing
completedRootedSourceFailsOnExhaustion
    root budget exhausted
    with NatP._<?_
      (completedRootedSourceWork root)
      budget
... | yes fits =
  ⊥-elim (NatP.<⇒≱ fits exhausted)
... | no doesNotFit =
  refl

------------------------------------------------------------------------
-- Still unpaid:
--  * one packed, arity-tagged TransitionTableCandidate;
--  * its real formula-rewrite representatives, arity/terminal admission;
--  * a restricted instruction machine which EMITS that exact candidate;
--  * proof its machineStepCount dominates completedRootedSourceWork;
--  * the full direct-DP evaluation + machine + payload strict inequality;
--  * an independent reason for success on the actual candidate-coupled root.
------------------------------------------------------------------------
