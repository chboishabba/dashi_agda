module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinStateWidthLowerExact where

------------------------------------------------------------------------
-- MACHINE STATE WIDTH <= ACTUAL GUARDED COOK BINARY QUOTATION WIDTH
--
-- The canonical finite-machine codec is one-hot in the state coordinate.
-- Every encoded tableau cell therefore contains at least StateWidth bits; every
-- guarded tableau has at least one column; the initial row is emitted as unit
-- clauses; and the existing CNF -> Cook -> binary chain preserves a lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact as Bridge
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinQuotationGrowthExact as Growth
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinBitCodeWidthLowerExact as BitLower

one : Nat
one = suc zero

oneBelowInitialInputCellCount :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine) →
  one ≤ Input.initialInputCellCount input
oneBelowInitialInputCellCount input = s≤s z≤n

oneBelowGuardedCols :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  one ≤ Guard.guardedInitialCols input steps
oneBelowGuardedCols input steps =
  NatP.≤-trans
    (oneBelowInitialInputCellCount input)
    (Growth.initialCellsBelowGuardedCols input steps)

positiveMultiplierLower :
  ∀ (width count : Nat) →
  one ≤ count →
  width ≤ count * width
positiveMultiplierLower width zero ()
positiveMultiplierLower width (suc count) positive =
  NatP.m≤m+n width (count * width)

stateWidthBelowCellWidth :
  (machine : Local.ConcreteTapeMachine) →
  Canonical.StateWidth machine ≤ Canonical.CellWidth machine
stateWidthBelowCellWidth machine =
  NatP.≤-trans
    (NatP.m≤m+n
      (Canonical.StateWidth machine)
      (Canonical.SymbolWidth machine))
    (NatP.n≤1+n
      (Canonical.StateWidth machine + Canonical.SymbolWidth machine))

cellWidthBelowGuardedRowBits :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Canonical.CellWidth machine
  ≤ Decode.RowBitsWidth machine (Guard.guardedInitialCols input steps)
cellWidthBelowGuardedRowBits {machine} input steps =
  positiveMultiplierLower
    (Canonical.CellWidth machine)
    (Guard.guardedInitialCols input steps)
    (oneBelowGuardedCols input steps)

stateWidthBelowGuardedRowBits :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Canonical.StateWidth machine
  ≤ Decode.RowBitsWidth machine (Guard.guardedInitialCols input steps)
stateWidthBelowGuardedRowBits {machine} input steps =
  NatP.≤-trans
    (stateWidthBelowCellWidth machine)
    (cellWidthBelowGuardedRowBits input steps)

stateWidthBelowGuardedCookBitCode :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Canonical.StateWidth machine
  ≤
  Binary.formulaBitCodeLength
    (CookLevin.guardedCookFormula
      stateCoverage symbolCoverage nonempty input steps)
stateWidthBelowGuardedCookBitCode
    {machine} stateCoverage symbolCoverage nonempty input steps =
  NatP.≤-trans
    (stateWidthBelowGuardedRowBits input steps)
    (NatP.≤-trans
      (Growth.rowBitsBelowGlobalClauses
        stateCoverage symbolCoverage nonempty input steps)
      (NatP.≤-trans
        (Growth.cnfClauseCountBelowCookNodeCount globalFormula)
        (BitLower.cookNodeCountBelowBitCode
          (Bridge.cnfToCook globalFormula))))
  where
    cols : Nat
    cols = Guard.guardedInitialCols input steps

    initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)
    initialTarget =
      Sound.guardedInitialBits stateCoverage symbolCoverage input steps

    globalFormula : CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
    globalFormula =
      Global.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty steps cols initialTarget

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- Any same-object self-generator that uses the repository's one-hot coded state
-- carrier must include at least its own state-code width in the resulting Cook
-- binary quotation.  This is the missing generic lower-bound ingredient for
-- auditing full-table-baked self-generation.
------------------------------------------------------------------------
