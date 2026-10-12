module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinBitCodeWidthLowerExact where

------------------------------------------------------------------------
-- GUARDED TABLEAU WIDTH <= ACTUAL COOK FORMULA BINARY CODE LENGTH
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat.Base using (_≤_)
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
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinarySizeLowerBoundExact as BinaryLower

cookNodeCountBelowBitCode :
  (formula : Cook.BooleanFormula) →
  FormulaSize.formulaNodeCount formula
  ≤ Binary.formulaBitCodeLength formula
cookNodeCountBelowBitCode formula =
  NatP.≤-trans
    nodesBelowThreeNodes
    (BinaryLower.binaryCodeAtLeastThreeBitsPerNode formula)
  where
    nodesBelowThreeNodes :
      FormulaSize.formulaNodeCount formula
      ≤ BinaryLower.three * FormulaSize.formulaNodeCount formula
    nodesBelowThreeNodes =
      NatP.≤-trans
        (NatP.m≤m*n
          (FormulaSize.formulaNodeCount formula)
          BinaryLower.three)
        (NatP.≤-reflexive
          (NatP.*-comm
            (FormulaSize.formulaNodeCount formula)
            BinaryLower.three))

guardedColsBelowCookFormulaBitCode :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Guard.guardedInitialCols input steps
  ≤
  Binary.formulaBitCodeLength
    (CookLevin.guardedCookFormula
      stateCoverage symbolCoverage nonempty input steps)
guardedColsBelowCookFormulaBitCode
    {machine}
    stateCoverage symbolCoverage nonempty input steps =
  NatP.≤-trans
    (Growth.guardedColsBelowRowBits input steps)
    (NatP.≤-trans
      (Growth.rowBitsBelowGlobalClauses
        stateCoverage symbolCoverage nonempty input steps)
      (NatP.≤-trans
        (Growth.cnfClauseCountBelowCookNodeCount globalFormula)
        (cookNodeCountBelowBitCode
          (Bridge.cnfToCook globalFormula))))
  where
    cols : Nat
    cols = Guard.guardedInitialCols input steps

    initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)
    initialTarget =
      Sound.guardedInitialBits
        stateCoverage symbolCoverage input steps

    globalFormula :
      CNF.CNF (Endpoint.ExtendedGlobalWidth machine steps cols)
    globalFormula =
      Global.globalCookLevinCNF
        stateCoverage symbolCoverage nonempty steps cols initialTarget

------------------------------------------------------------------------
-- This lower bound needs no nonempty-seed premise. It charges the full guarded
-- tableau width, including the 2*T blank-margin columns, into the actual binary
-- Cook quotation.
------------------------------------------------------------------------
