module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientMemoizedDPExact where

------------------------------------------------------------------------
-- EXPLICIT MEMOIZED EXECUTION OF THE RESTRICTION-QUOTIENT DP
--
-- The semantic owner defines
--
--   V_(d+1)(q) = V_d(step(q,false)) OR V_d(step(q,true))
--
-- recursively.  That definition proves correctness but, evaluated naively,
-- need not share repeated subproblems.
--
-- Here every depth layer is MATERIALIZED as a finite vector indexed by states.
-- One layer performs exactly stateCount cell updates.  The canonical trace to
-- depth d therefore charges exactly
--
--   (d + 1) * stateCount
--
-- updates, matching the existing dynamic-table cell count.
--
-- Lookup in the materialized final layer is proved equal to the semantic
-- quotientTruthAtDepth value.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
import Data.Fin.Base as FinBase
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP

------------------------------------------------------------------------
-- Tiny self-contained Fin tabulation, to make the execution object explicit.
------------------------------------------------------------------------

tabulateFin :
  ∀ {A : Set} {count : Nat} →
  (Fin count → A) →
  Vec A count
tabulateFin {count = zero} function =
  []
tabulateFin {count = suc count} function =
  function FinBase.zero
  ∷
  tabulateFin
    (λ index →
      function (FinBase.suc index))

lookupTable :
  ∀ {A : Set} {count : Nat} →
  Vec A count →
  Fin count →
  A
lookupTable (head ∷ tail) FinBase.zero =
  head
lookupTable (head ∷ tail) (FinBase.suc index) =
  lookupTable tail index

lookupTabulateFin :
  ∀ {A : Set} {count : Nat}
    (function : Fin count → A)
    (index : Fin count) →
  lookupTable
      (tabulateFin function)
      index
  ≡
  function index
lookupTabulateFin
    {count = suc count}
    function
    FinBase.zero =
  refl
lookupTabulateFin
    {count = suc count}
    function
    (FinBase.suc index) =
  lookupTabulateFin
    (λ inner →
      function (FinBase.suc inner))
    index

------------------------------------------------------------------------
-- One materialized state layer.
------------------------------------------------------------------------

StateTable :
  Nat →
  Set
StateTable stateCount =
  Vec Bool stateCount

terminalTable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle} →
  DP.TerminalStateLabelling quotient oracle →
  StateTable (Quotient.stateCount quotient)
terminalTable quotient labels =
  tabulateFin
    (DP.terminalTruth labels)

advanceTable :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  StateTable (Quotient.stateCount quotient) →
  StateTable (Quotient.stateCount quotient)
advanceTable quotient previous =
  tabulateFin
    (λ state →
      SAT.orBool
        (lookupTable previous
          (Quotient.step quotient state
            Agda.Builtin.Bool.false))
        (lookupTable previous
          (Quotient.step quotient state
            Agda.Builtin.Bool.true)))

------------------------------------------------------------------------
-- Materialized table at one depth.
------------------------------------------------------------------------

memoTableAtDepth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle} →
  DP.TerminalStateLabelling quotient oracle →
  Nat →
  StateTable (Quotient.stateCount quotient)
memoTableAtDepth quotient labels zero =
  terminalTable quotient labels
memoTableAtDepth quotient labels (suc depth) =
  advanceTable quotient
    (memoTableAtDepth quotient labels depth)

------------------------------------------------------------------------
-- Table lookup equals the semantic recursive DP.
------------------------------------------------------------------------

memoLookupExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle)
    (depth : Nat)
    (state : Fin (Quotient.stateCount quotient)) →
  lookupTable
      (memoTableAtDepth quotient labels depth)
      state
  ≡
  DP.quotientTruthAtDepth
      quotient
      labels
      depth
      state
memoLookupExact quotient labels zero state =
  lookupTabulateFin
    (DP.terminalTruth labels)
    state
memoLookupExact quotient labels (suc depth) state =
  trans
    (lookupTabulateFin
      (λ current →
        SAT.orBool
          (lookupTable
            (memoTableAtDepth quotient labels depth)
            (Quotient.step quotient current
              Agda.Builtin.Bool.false))
          (lookupTable
            (memoTableAtDepth quotient labels depth)
            (Quotient.step quotient current
              Agda.Builtin.Bool.true)))
      state)
    (cong₂
      SAT.orBool
      (memoLookupExact
        quotient
        labels
        depth
        (Quotient.step quotient state
          Agda.Builtin.Bool.false))
      (memoLookupExact
        quotient
        labels
        depth
        (Quotient.step quotient state
          Agda.Builtin.Bool.true)))

------------------------------------------------------------------------
-- Typed construction trace with exact cell-update charge.
------------------------------------------------------------------------

data MemoizedTableTrace
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle) :
    (depth : Nat) →
    StateTable (Quotient.stateCount quotient) →
    Nat →
    Set where

  terminalTrace :
    MemoizedTableTrace
      quotient
      labels
      zero
      (terminalTable quotient labels)
      (Quotient.stateCount quotient)

  advanceTrace :
    ∀ {depth previousCost}
      {previous :
        StateTable
          (Quotient.stateCount quotient)} →
    MemoizedTableTrace
      quotient
      labels
      depth
      previous
      previousCost →
    MemoizedTableTrace
      quotient
      labels
      (suc depth)
      (advanceTable quotient previous)
      (Quotient.stateCount quotient
        + previousCost)

------------------------------------------------------------------------
-- Canonical trace cost is exactly (depth+1)*stateCount.
------------------------------------------------------------------------

canonicalMemoizedTrace :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle)
    (depth : Nat) →
  MemoizedTableTrace
    quotient
    labels
    depth
    (memoTableAtDepth quotient labels depth)
    (suc depth
      * Quotient.stateCount quotient)
canonicalMemoizedTrace quotient labels zero =
  terminalTrace
canonicalMemoizedTrace quotient labels (suc depth) =
  advanceTrace
    (canonicalMemoizedTrace
      quotient
      labels
      depth)

------------------------------------------------------------------------
-- Exact agreement with the pre-existing represented table cell count.
------------------------------------------------------------------------

memoizedUpdateCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  Nat
memoizedUpdateCount {rootVariables} quotient =
  suc rootVariables
  * Quotient.stateCount quotient

memoizedUpdateCountIsDynamicTableCellCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root) →
  memoizedUpdateCount quotient
  ≡
  DP.quotientDynamicTableCellCount quotient
memoizedUpdateCountIsDynamicTableCellCount quotient =
  refl

------------------------------------------------------------------------
-- Root lookup from the explicit table equals the existing semantic root DP.
------------------------------------------------------------------------

memoizedRootTruth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle} →
  DP.TerminalStateLabelling quotient oracle →
  Bool
memoizedRootTruth
    {rootVariables}
    quotient
    labels =
  lookupTable
    (memoTableAtDepth
      quotient
      labels
      rootVariables)
    (Quotient.classify
      quotient
      DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact.restrictionRoot)

memoizedRootTruthExact :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle}
    (labels : DP.TerminalStateLabelling quotient oracle) →
  memoizedRootTruth quotient labels
  ≡
  DP.quotientTruthAtDepth
    quotient
    labels
    rootVariables
    (Quotient.classify
      quotient
      DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact.restrictionRoot)
memoizedRootTruthExact
    {rootVariables}
    quotient
    labels =
  memoLookupExact
    quotient
    labels
    rootVariables
    (Quotient.classify
      quotient
      DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact.restrictionRoot)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The direct-DP authority no longer relies on evaluator sharing as an
-- implementation assumption.  A concrete table is materialized, with one
-- charged update per (depth,state) cell, and its final lookup is exactly the
-- previously proved semantic quotient DP.
------------------------------------------------------------------------
