module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinQuotationGrowthExact where

------------------------------------------------------------------------
-- THE ACTUAL CONCRETE COOK--LEVIN CONSTRUCTOR IS STRICTLY GROWING
--
-- For any nonempty literal tape input:
--
--   payload symbols
--      < guarded initial cells
--      <= guarded columns
--      <= encoded initial-row bits
--      = initial unit clauses
--      <= total global CNF clauses
--      <= Cook AST nodes
--      <= quoted binary bits.
--
-- Thus the ordinary full-tableau Cook--Levin constructor already grows beyond
-- the input payload before transition constraints are charged.
--
-- This is a theorem about the ACTUAL constructor welded in
-- ConcreteTapeCookLevinCookFormulaExact, not a generic size assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as CNFSize
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeClosedExact as Closed
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact as Bridge
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact as CookLevin
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinarySizeLowerBoundExact as BinaryLower

------------------------------------------------------------------------
-- CNF -> Cook AST always has at least one AST node per CNF clause.
------------------------------------------------------------------------

cnfClauseCountBelowCookNodeCount :
  ∀ {width : Nat}
    (formula : CNF.CNF width) →
  CNFSize.listLength formula
  ≤
  FormulaSize.formulaNodeCount
    (Bridge.cnfToCook formula)
cnfClauseCountBelowCookNodeCount [] =
  z≤n
cnfClauseCountBelowCookNodeCount
    (clause ∷ clauses) =
  NatP.≤-trans
    (s≤s
      (cnfClauseCountBelowCookNodeCount
        clauses))
    (s≤s
      (NatP.m≤n+m
        (FormulaSize.formulaNodeCount
          (Bridge.cnfToCook clauses))
        (FormulaSize.formulaNodeCount
          (Bridge.clauseToCook clause))))

------------------------------------------------------------------------
-- Initial endpoint clauses are a literal sub-list of the global formula.
------------------------------------------------------------------------

initialClausesBelowGlobalClauses :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty :
      Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget :
      CNF.Bits
        (Decode.RowBitsWidth machine cols)) →
  CNFSize.listLength
    (Endpoint.initialEndpointCNF initialTarget)
  ≤
  CNFSize.listLength
    (Global.globalCookLevinCNF
      stateCoverage
      symbolCoverage
      nonempty
      steps
      cols
      initialTarget)
initialClausesBelowGlobalClauses
    stateCoverage
    symbolCoverage
    nonempty
    steps
    cols
    initialTarget
    rewrite
      Closed.appendLength
        (Global.liftTransitionCNF
          stateCoverage symbolCoverage
          nonempty steps cols)
        (Placed.append
          (Endpoint.initialEndpointCNF initialTarget)
          (Endpoint.acceptingEndpointCNF
            stateCoverage symbolCoverage))
      |
      Closed.appendLength
        (Endpoint.initialEndpointCNF initialTarget)
        (Endpoint.acceptingEndpointCNF
          stateCoverage symbolCoverage) =
  NatP.≤-trans
    (NatP.m≤m+n
      (CNFSize.listLength
        (Endpoint.initialEndpointCNF initialTarget))
      (CNFSize.listLength
        (Endpoint.acceptingEndpointCNF
          stateCoverage symbolCoverage)))
    (NatP.m≤n+m
      (CNFSize.listLength
        (Endpoint.initialEndpointCNF initialTarget)
        +
        CNFSize.listLength
          (Endpoint.acceptingEndpointCNF
            stateCoverage symbolCoverage))
      (CNFSize.listLength
        (Global.liftTransitionCNF
          stateCoverage symbolCoverage
          nonempty steps cols)))

------------------------------------------------------------------------
-- Payload symbols are strictly fewer than guarded columns for nonempty input.
------------------------------------------------------------------------

nonemptyPayloadStrictlyBelowInitialCells :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine)) →
  Input.inputPayloadLength
    (symbol ∷ rest)
  <
  Input.initialInputCellCount
    (symbol ∷ rest)
nonemptyPayloadStrictlyBelowInitialCells
    symbol
    rest
    rewrite
      Input.initialInputCellCount_nonempty
        symbol rest =
  NatP.n<1+n
    (suc (Canonical.listLength rest))

initialCellsBelowGuardedCols :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Input.initialInputCellCount input
  ≤
  Guard.guardedInitialCols input steps
initialCellsBelowGuardedCols
    input
    steps =
  NatP.m≤m+n
    (Input.initialInputCellCount input)
    (suc (suc zero) * steps)

nonemptyPayloadStrictlyBelowGuardedCols :
  ∀ {machine : Local.ConcreteTapeMachine}
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine))
    (steps : Nat) →
  Input.inputPayloadLength
    (symbol ∷ rest)
  <
  Guard.guardedInitialCols
    (symbol ∷ rest)
    steps
nonemptyPayloadStrictlyBelowGuardedCols
    symbol
    rest
    steps =
  NatP.<-≤-trans
    (nonemptyPayloadStrictlyBelowInitialCells
      symbol rest)
    (initialCellsBelowGuardedCols
      (symbol ∷ rest)
      steps)

------------------------------------------------------------------------
-- Every guarded column contributes at least one encoded row bit.
------------------------------------------------------------------------

guardedColsBelowRowBits :
  ∀ {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Guard.guardedInitialCols input steps
  ≤
  Decode.RowBitsWidth
    machine
    (Guard.guardedInitialCols input steps)
guardedColsBelowRowBits
    {machine}
    input
    steps =
  NatP.m≤m*n
    (Guard.guardedInitialCols input steps)
    (Canonical.CellWidth machine)

------------------------------------------------------------------------
-- Initial row bits become exactly that many unit clauses.
------------------------------------------------------------------------

rowBitsBelowGlobalClauses :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty :
      Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Decode.RowBitsWidth
    machine
    (Guard.guardedInitialCols input steps)
  ≤
  CNFSize.listLength
    (Global.globalCookLevinCNF
      stateCoverage
      symbolCoverage
      nonempty
      steps
      (Guard.guardedInitialCols input steps)
      (Sound.guardedInitialBits
        stateCoverage
        symbolCoverage
        input
        steps))
rowBitsBelowGlobalClauses
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps =
  subst
    (λ initialClauseCount →
      initialClauseCount
      ≤
      CNFSize.listLength globalFormula)
    (Closed.initialEndpointClauseCount initialTarget)
    (initialClausesBelowGlobalClauses
      stateCoverage
      symbolCoverage
      nonempty
      steps
      cols
      initialTarget)
  where
    cols : Nat
    cols =
      Guard.guardedInitialCols input steps

    initialTarget :
      CNF.Bits
        (Decode.RowBitsWidth machine cols)
    initialTarget =
      Sound.guardedInitialBits
        stateCoverage
        symbolCoverage
        input
        steps

    globalFormula :
      CNF.CNF
        (Endpoint.ExtendedGlobalWidth
          machine steps cols)
    globalFormula =
      Global.globalCookLevinCNF
        stateCoverage
        symbolCoverage
        nonempty
        steps
        cols
        initialTarget

------------------------------------------------------------------------
-- Main AST growth theorem.
------------------------------------------------------------------------

nonemptyPayloadStrictlyBelowCookFormulaNodes :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty :
      Selector.NonemptyRuleTable machine)
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine))
    (steps : Nat) →
  Input.inputPayloadLength
    (symbol ∷ rest)
  <
  FormulaSize.formulaNodeCount
    (CookLevin.guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      (symbol ∷ rest)
      steps)
nonemptyPayloadStrictlyBelowCookFormulaNodes
    {machine}
    stateCoverage
    symbolCoverage
    nonempty
    symbol
    rest
    steps =
  NatP.<-≤-trans
    payloadBelowBits
    clausesBelowNodes
  where
    input : Input.InputWord machine
    input =
      symbol ∷ rest

    cols : Nat
    cols =
      Guard.guardedInitialCols input steps

    initialTarget :
      CNF.Bits
        (Decode.RowBitsWidth machine cols)
    initialTarget =
      Sound.guardedInitialBits
        stateCoverage
        symbolCoverage
        input
        steps

    globalFormula :
      CNF.CNF
        (Endpoint.ExtendedGlobalWidth
          machine steps cols)
    globalFormula =
      Global.globalCookLevinCNF
        stateCoverage
        symbolCoverage
        nonempty
        steps
        cols
        initialTarget

    payloadBelowBits :
      Input.inputPayloadLength input
      <
      CNFSize.listLength globalFormula
    payloadBelowBits =
      NatP.<-≤-trans
        (NatP.<-≤-trans
          (nonemptyPayloadStrictlyBelowGuardedCols
            symbol rest steps)
          (guardedColsBelowRowBits
            input steps))
        (rowBitsBelowGlobalClauses
          stateCoverage
          symbolCoverage
          nonempty
          input
          steps)

    clausesBelowNodes :
      CNFSize.listLength globalFormula
      ≤
      FormulaSize.formulaNodeCount
        (Bridge.cnfToCook globalFormula)
    clausesBelowNodes =
      cnfClauseCountBelowCookNodeCount
        globalFormula

------------------------------------------------------------------------
-- Binary quotation is strictly longer than the nonempty payload too.
------------------------------------------------------------------------

nonemptyPayloadStrictlyBelowCookFormulaBitCode :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage
        (Local.finiteSymbol machine))
    (nonempty :
      Selector.NonemptyRuleTable machine)
    (symbol : Local.Symbol machine)
    (rest : List (Local.Symbol machine))
    (steps : Nat) →
  Input.inputPayloadLength
    (symbol ∷ rest)
  <
  Binary.formulaBitCodeLength
    (CookLevin.guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      (symbol ∷ rest)
      steps)
nonemptyPayloadStrictlyBelowCookFormulaBitCode
    stateCoverage
    symbolCoverage
    nonempty
    symbol
    rest
    steps =
  NatP.<-≤-trans
    (nonemptyPayloadStrictlyBelowCookFormulaNodes
      stateCoverage
      symbolCoverage
      nonempty
      symbol
      rest
      steps)
    nodeCountBelowCode
  where
    formula =
      CookLevin.guardedCookFormula
        stateCoverage
        symbolCoverage
        nonempty
        (symbol ∷ rest)
        steps

    nodesBelowThreeNodes :
      FormulaSize.formulaNodeCount formula
      ≤
      BinaryLower.three
      * FormulaSize.formulaNodeCount formula
    nodesBelowThreeNodes =
      NatP.≤-trans
        (NatP.m≤m*n
          (FormulaSize.formulaNodeCount formula)
          BinaryLower.three)
        (NatP.≤-reflexive
          (NatP.*-comm
            (FormulaSize.formulaNodeCount formula)
            BinaryLower.three))

    nodeCountBelowCode :
      FormulaSize.formulaNodeCount formula
      ≤
      Binary.formulaBitCodeLength formula
    nodeCountBelowCode =
      NatP.≤-trans
        nodesBelowThreeNodes
        (BinaryLower.binaryCodeAtLeastThreeBitsPerNode
          formula)

------------------------------------------------------------------------
-- Research consequence.
--
-- The ordinary full-tableau concrete Cook--Levin constructor is strictly
-- growing already from its initial-row obligations.  If a binary-input machine
-- uses one input symbol per quoted formula bit, then the raw equation
--
--   input = encodeFormulaBits(guardedCookFormula machine input steps)
--
-- cannot hold for nonempty input.
--
-- Therefore the self-diagonal route must use a behavioural/semantic fixed
-- point and then exploit the quotient/strict-representative machinery to close
-- resources; literal source-string equality is not the right fixed point.
------------------------------------------------------------------------
