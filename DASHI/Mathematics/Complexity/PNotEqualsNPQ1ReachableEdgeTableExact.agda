module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableEdgeTableExact where

------------------------------------------------------------------------
-- ACTUAL ROOT-REACHABLE FINITE TRANSITION AND TERMINAL ROWS
--
-- The state carrier is NOT Fin(2^(2^r)). It is Fin(length of the
-- deduplicated truth-table keys generated from the selected formula root).
--
-- Every source index at a nonterminal layer emits two concrete successor
-- indices with exact decoded Shannon semantics. No transition is postulated
-- and no SAT oracle decides membership. The derived completeness theorem for
-- keyOnlyStep supplies an indexed target for each enumerated row.
--
-- At the final arity-zero layer every numeric state emits a computed terminal
-- label, with equality to actual root-derived formula evaluation.
--
-- The run/budget connection to DirectDPChargedConstructionRun remains open:
-- materializing the rows is not equivalent to a charged interpreter trace.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (List; map; length)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1RootedExhaustiveMergeExact as Root
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableNumericQuotientExact as Reachable
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1KeyOnlyTransitionExact as Key
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableTerminalAdmissionExact as Terminal
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1CanonicalRepresentativeSelectionExact as Rep
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1TruthTableRepairGeneratorExact as Truth
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact as Graph
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as Future

------------------------------------------------------------------------
-- A row contains the ACTUAL numeric source, both numeric targets, and the
-- two exact local equations needed for future-semantic admission.
------------------------------------------------------------------------

record ReachableEdgeRow
    {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining)) : Set where
  constructor reachable-edge-row
  field
    source : Reachable.ReachableNumericState previous
    falseTarget : Reachable.ReachableNumericState (Root.descend previous)
    trueTarget : Reachable.ReachableNumericState (Root.descend previous)

    falseTargetExact :
      Reachable.decodeReachableState (Root.descend previous)
        falseTarget
      ≡
      Truth.restrictTruthTable false
        (Reachable.decodeReachableState previous source)

    trueTargetExact :
      Reachable.decodeReachableState (Root.descend previous)
        trueTarget
      ≡
      Truth.restrictTruthTable true
        (Reachable.decodeReachableState previous source)

open ReachableEdgeRow public

------------------------------------------------------------------------
-- No opaque witness is supplied: both successors are extracted from the
-- source-index-only executable key-search completeness theorem.
------------------------------------------------------------------------

emitReachableEdge :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState previous) →
  ReachableEdgeRow previous
emitReachableEdge previous source =
  reachable-edge-row
    source
    (proj₁ falseResult)
    (proj₁ trueResult)
    (proj₂ falseResult)
    (proj₂ trueResult)
  where
    falseResult :
      Σ
        (Reachable.ReachableNumericState (Root.descend previous))
        (λ target →
          Reachable.decodeReachableState (Root.descend previous) target
          ≡
          Truth.restrictTruthTable false
            (Reachable.decodeReachableState previous source))
    falseResult =
      proj₁ (Key.keyOnlyStepComplete false previous source)

    trueResult :
      Σ
        (Reachable.ReachableNumericState (Root.descend previous))
        (λ target →
          Reachable.decodeReachableState (Root.descend previous) target
          ≡
          Truth.restrictTruthTable true
            (Reachable.decodeReachableState previous source))
    trueResult =
      proj₁ (Key.keyOnlyStepComplete true previous source)

------------------------------------------------------------------------
-- Enumerate ALL finite source IDs: there are no externally supplied rows.
------------------------------------------------------------------------

allReachableEdgeRows :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining)) →
  List (ReachableEdgeRow previous)
allReachableEdgeRows previous =
  map (emitReachableEdge previous)
    (Graph.allFin
      (length (Root.rootedMergedSemanticKeys previous)))

allReachableEdgeRowsCover :
  ∀ {rootVariables remaining : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (previous : Root.DescentPath root (suc remaining))
    (source : Reachable.ReachableNumericState previous) →
  Graph.Listed
    (emitReachableEdge previous source)
    (allReachableEdgeRows previous)
allReachableEdgeRowsCover previous source =
  Graph.mapPreservesListed
    (emitReachableEdge previous)
    (Graph.allFinCovers source)

------------------------------------------------------------------------
-- At arity zero, emit one row per canonical reachable state.
------------------------------------------------------------------------

record ReachableTerminalRow
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (terminalPath : Root.DescentPath root zero) : Set where
  constructor reachable-terminal-row
  field
    source : Reachable.ReachableNumericState terminalPath
    label : Bool
    labelExact :
      let rep = Rep.representativeOfIndex terminalPath source
      in
      label
      ≡
      SAT.evaluate
        (Family.currentFormula
          (Width.node
            (Rep.node rep)))
        Future.emptyAssignment

open ReachableTerminalRow public

emitReachableTerminal :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (terminalPath : Root.DescentPath root zero)
    (source : Reachable.ReachableNumericState terminalPath) →
  ReachableTerminalRow terminalPath
emitReachableTerminal terminalPath source =
  reachable-terminal-row
    source
    (Terminal.reachableTerminalLabel terminalPath source)
    (Terminal.reachableTerminalLabelExact terminalPath source)

allReachableTerminalRows :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (terminalPath : Root.DescentPath root zero) →
  List (ReachableTerminalRow terminalPath)
allReachableTerminalRows terminalPath =
  map (emitReachableTerminal terminalPath)
    (Graph.allFin
      (length (Root.rootedMergedSemanticKeys terminalPath)))

allReachableTerminalRowsCover :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (terminalPath : Root.DescentPath root zero)
    (source : Reachable.ReachableNumericState terminalPath) →
  Graph.Listed
    (emitReachableTerminal terminalPath source)
    (allReachableTerminalRows terminalPath)
allReachableTerminalRowsCover terminalPath source =
  Graph.mapPreservesListed
    (emitReachableTerminal terminalPath)
    (Graph.allFinCovers source)

------------------------------------------------------------------------
-- These rows are a concrete root-reachable quotient table per graded layer.
-- Still OPEN: pack all layers into one finite DirectDP candidate, prove
-- state-arity/terminal admission, provide a typed interpreter trace producing
-- the exact packed candidate, and prove its strict all-overhead resource fit.
------------------------------------------------------------------------
