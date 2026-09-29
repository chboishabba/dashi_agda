module DASHI.Mathematics.Complexity.PNotEqualsNPQ1IndexedGraphCellBudgetExact where

------------------------------------------------------------------------
-- FINITE INDEXED GRAPH: EXISTENCE VERSUS BUDGET ADMISSION
--
-- Source: PNotEqualsNPQ1ExplicitIndexedGraphExact.buildReferenceGraph
-- constructs all finite state IDs, all transitions and all terminal labels.
--
-- Here its literal graph storage is counted and compared with an explicit
-- strict bound. A graph always exists, but the budgeted construction is allowed
-- to return nothing.
--
-- This is ONLY a graph-cell charge. It is not a bound on formula evaluation,
-- truth-table generation, deduplication, machine execution, or Q1 successor
-- measure. In particular it is NOT DirectDPChargedStateConstructor.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_<_)
import Data.Nat.Properties as NatP
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExplicitIndexedGraphExact as Graph

------------------------------------------------------------------------
-- Account for one state cell, two directed cells per emitted transition,
-- and one terminal-label cell. Each count is computed from built Lists.
------------------------------------------------------------------------

graphStorageCells :
  ∀ {bound : Nat} →
  Graph.ReferenceGraph bound →
  Nat
graphStorageCells graph =
  length (Graph.states graph)
  + (length (Graph.transitions graph)
     + length (Graph.transitions graph))
  + length (Graph.terminals graph)

literalGraphCells :
  (bound : Nat) →
  Nat
literalGraphCells bound =
  graphStorageCells
    (Graph.buildReferenceGraph bound)

------------------------------------------------------------------------
-- A real decidable strict gate; no success is postulated.
------------------------------------------------------------------------

budgetedReferenceGraph :
  (bound budget : Nat) →
  Maybe
    (Σ
      (Graph.ReferenceGraph bound)
      (λ graph →
        graphStorageCells graph < budget))
budgetedReferenceGraph bound budget
    with NatP._<?_
      (literalGraphCells bound)
      budget
... | yes fits =
  just (Graph.buildReferenceGraph bound , fits)
... | no doesNotFit =
  nothing

------------------------------------------------------------------------
-- Successful return *contains* the strict storage certificate, while graph
-- construction remains total even when the gate returns nothing.
------------------------------------------------------------------------

budgetedGraphSuccessfulReturnFits :
  ∀ {bound budget : Nat}
    {result :
      Σ
        (Graph.ReferenceGraph bound)
        (λ graph →
          graphStorageCells graph < budget)} →
  budgetedReferenceGraph bound budget ≡ just result →
  graphStorageCells (proj₁ result) < budget
budgetedGraphSuccessfulReturnFits
    {result = result}
    successful =
  proj₂ result

------------------------------------------------------------------------
-- The separate Clay-critical obligations are:
--
--   * reachable-state quotient versus this all-function supergraph;
--   * actual machine interpreter cost for materialization/indexing;
--   * Q1 arity/terminal/rewrite admission on the candidate's own root;
--   * the strict ALL-overhead and next-measure recurrence;
--   * a noncircular guarantee that this gate succeeds at that same root.
--
-- None is manufactured by checking graphStorageCells.
------------------------------------------------------------------------
