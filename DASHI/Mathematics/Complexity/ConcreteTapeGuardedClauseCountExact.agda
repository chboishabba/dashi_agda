module DASHI.Mathematics.Complexity.ConcreteTapeGuardedClauseCountExact where

------------------------------------------------------------------------
-- EXACT ADDITIVE CLAUSE COST OF THE REAL GUARDED GLOBAL FORMULA.
--
-- Original global-CNF bound: existing ConcreteTapeCookLevinSizeClosedExact.
-- New endcaps: two identical machine-constant local truth-table templates
-- per physical row; (steps + 1) rows; no extra SAT variables.
-- This is a literal list-length proof on the original CNF, not a
-- claim that the full uniform binary-tape compiler clock is complete.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Data.Nat using (_∸_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalEndcapCNFExact as Endcap
import DASHI.Mathematics.Complexity.ConcreteTapeGuardedGlobalCookLevinCNFExact as Guarded
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeClosedExact as Closed
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as Size
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

localEndcapClauseCount : Local.ConcreteTapeMachine → Nat
localEndcapClauseCount machine =
  Size.listLength (Endcap.canonicalPlainEndcapCNF {machine})

twoEndcapsPerRow : Local.ConcreteTapeMachine → Nat
twoEndcapsPerRow machine =
  localEndcapClauseCount machine + localEndcapClauseCount machine

localEndcapTruthTableBound :
  (machine : Local.ConcreteTapeMachine) →
  Σ Nat (λ slack →
    localEndcapClauseCount machine + slack
    ≡ 2 ^ Canonical.CellWidth machine)
localEndcapTruthTableBound machine =
  Size.truthTableCNF_clause_bound (Endcap.plainEndcapPredicate {machine})

onePhysicalCellCNFCount :
  ∀ {machine steps cols rowIndex colIndex}
    (rowSlot : Endcap.Global.Slot rowIndex (suc steps))
    (cellSlot : Endcap.Global.Slot colIndex cols) →
  Size.listLength
    (Endcap.globalRowCellPlainCNF rowSlot cellSlot)
  ≡ localEndcapClauseCount machine
onePhysicalCellCNFCount rowSlot cellSlot =
  Closed.renameCNF_length
    (Endcap.rowCellExtendedRename rowSlot cellSlot)
    Endcap.canonicalPlainEndcapCNF

oneRowEndcapsCNFCount :
  ∀ {machine steps rowIndex}
    (colsMinusOne : Nat)
    (rowSlot : Endcap.Global.Slot rowIndex (suc steps)) →
  Size.listLength
    (Endcap.globalRowEndcapsCNF colsMinusOne rowSlot)
  ≡ twoEndcapsPerRow machine
oneRowEndcapsCNFCount colsMinusOne rowSlot =
  trans
    (Closed.appendLength
      (Endcap.globalRowCellPlainCNF rowSlot Endcap.Global.here)
      (Endcap.globalRowCellPlainCNF rowSlot
        (Endcap.lastPhysicalColumn colsMinusOne)))
    (cong₂ _+_
      (onePhysicalCellCNFCount rowSlot Endcap.Global.here)
      (onePhysicalCellCNFCount rowSlot
        (Endcap.lastPhysicalColumn colsMinusOne)))

shiftRowSlotsCount :
  ∀ {count} (rows : List (Endcap.SomeRowSlot count)) →
  Size.listLength (Endcap.shiftRowSlots rows)
  ≡ Size.listLength rows
shiftRowSlotsCount [] = refl
shiftRowSlotsCount (r ∷ rs)
  rewrite shiftRowSlotsCount rs = refl

allPhysicalRowsCount :
  (count : Nat) →
  Size.listLength (Endcap.allPhysicalRows count) ≡ count
allPhysicalRowsCount zero = refl
allPhysicalRowsCount (suc n)
  rewrite shiftRowSlotsCount (Endcap.allPhysicalRows n)
        | allPhysicalRowsCount n =
  refl

appendAllEndcapsCount :
  ∀ {machine steps}
    (colsMinusOne : Nat)
    (rows : List (Endcap.SomeRowSlot (suc steps))) →
  Size.listLength
    (Endcap.appendAllRowEndcaps {machine = machine} colsMinusOne rows)
  ≡ Size.listLength rows * twoEndcapsPerRow machine
appendAllEndcapsCount colsMinusOne [] = refl
appendAllEndcapsCount {machine = machine}
    colsMinusOne (Endcap.some-row-slot slot ∷ rest)
  rewrite Closed.appendLength
    (Endcap.globalRowEndcapsCNF colsMinusOne slot)
    (Endcap.appendAllRowEndcaps colsMinusOne rest)
          | oneRowEndcapsCNFCount colsMinusOne slot
          | appendAllEndcapsCount colsMinusOne rest = refl

globalAllRowsEndcapsCount :
  ∀ {machine steps}
    (colsMinusOne : Nat) →
  Size.listLength
    (Endcap.globalAllRowsEndcapsCNF {machine = machine}
      {steps = steps} colsMinusOne)
  ≡ (suc steps) * twoEndcapsPerRow machine
globalAllRowsEndcapsCount {steps = steps} colsMinusOne
  rewrite appendAllEndcapsCount colsMinusOne
    (Endcap.allPhysicalRows (suc steps))
        | allPhysicalRowsCount (suc steps) = refl

guardedGlobalExactClauseCount :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne))) →
  Size.listLength
    (Guarded.guardedGlobalCookLevinCNF
      stateCoverage symbolCoverage nonempty
      steps colsMinusOne initialTarget)
  ≡
    Size.listLength
      (GlobalCNF.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty
        steps (suc colsMinusOne) initialTarget)
    + (suc steps) * twoEndcapsPerRow machine
guardedGlobalExactClauseCount
    stateCoverage symbolCoverage nonempty steps colsMinusOne initialTarget =
  trans
    (Closed.appendLength
      (GlobalCNF.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty
        steps (suc colsMinusOne) initialTarget)
      (Endcap.globalAllRowsEndcapsCNF colsMinusOne))
    (cong
      (λ n →
        Size.listLength
          (GlobalCNF.globalCookLevinCNF
            stateCoverage symbolCoverage nonempty
            steps (suc colsMinusOne) initialTarget) + n)
      (globalAllRowsEndcapsCount colsMinusOne))

guardedGlobalClauseBound :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps colsMinusOne : Nat)
    (initialTarget :
      CNF.Bits (Decode.RowBitsWidth machine (suc colsMinusOne))) →
  Σ Nat (λ slack →
    Size.listLength
      (Guarded.guardedGlobalCookLevinCNF
        stateCoverage symbolCoverage nonempty
        steps colsMinusOne initialTarget)
    + slack
    ≡
      ((steps * (suc colsMinusOne ∸ 2))
        * (2 ^ Selected.TransitionLocalWidth machine))
      + Decode.RowBitsWidth machine (suc colsMinusOne)
      + suc ((suc colsMinusOne) *
          (2 ^ Endpoint.AcceptanceLocalWidth machine))
      + ((suc steps) * twoEndcapsPerRow machine))
guardedGlobalClauseBound {machine}
    stateCoverage symbolCoverage nonempty steps colsMinusOne initialTarget
    with Closed.globalCookLevinClause_bound
      stateCoverage symbolCoverage nonempty
      steps (suc colsMinusOne) initialTarget
... | slack , originalBound =
  slack , proof
  where
    orig = Size.listLength
      (GlobalCNF.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty
        steps (suc colsMinusOne) initialTarget)
    extra = (suc steps) * twoEndcapsPerRow machine

    proof :
      Size.listLength
        (Guarded.guardedGlobalCookLevinCNF
          stateCoverage symbolCoverage nonempty
          steps colsMinusOne initialTarget)
      + slack
      ≡
        ((steps * (suc colsMinusOne ∸ 2))
          * (2 ^ Selected.TransitionLocalWidth machine))
        + Decode.RowBitsWidth machine (suc colsMinusOne)
        + suc ((suc colsMinusOne) *
            (2 ^ Endpoint.AcceptanceLocalWidth machine))
        + extra
    proof =
      trans
        (cong (λ n → n + slack)
          (guardedGlobalExactClauseCount
            stateCoverage symbolCoverage nonempty
            steps colsMinusOne initialTarget))
        (trans
          (NatP.+-assoc orig extra slack)
          (trans
            (cong (λ n → orig + n) (NatP.+-comm extra slack))
            (trans
              (sym (NatP.+-assoc orig slack extra))
              (cong (λ n → n + extra) originalBound))))
