module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinCookFormulaExact where

------------------------------------------------------------------------
-- CONCRETE TAPE COOK--LEVIN -> CLAY-CRITICAL COOK BOOLEANFORMULA
--
-- Existing exact-budget capstone:
--
--   guarded global CNF satisfiable
--      iff
--   actual accepting run of exactly T transitions.
--
-- Existing bridge:
--
--   fixed-width CNF satisfiable
--      iff
--   Cook.BooleanFormula satisfiable.
--
-- This owner composes them.
--
-- Main theorem:
--
--   Cook.Satisfiable (guardedCookFormula M x T)
--      iff
--   ExactBudgetAcceptingRun x T.
--
-- Thus the concrete machine/input/time-budget reduction now lands on the SAME
-- BooleanFormula carrier used by SATLowerBoundProducer and the self-diagonal
-- programme.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.FixedWidthCNFToCookFormulaExact as Bridge

------------------------------------------------------------------------
-- Literal Cook formula for one concrete machine/input/exact budget.
------------------------------------------------------------------------

guardedCookFormula :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Cook.BooleanFormula
guardedCookFormula
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps =
  Bridge.cnfToCook
    (GlobalCNF.globalCookLevinCNF
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

------------------------------------------------------------------------
-- Cook satisfiability -> exact accepting run.
------------------------------------------------------------------------

cookSatisfiableToExactBudgetRun :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Cook.Satisfiable
    (guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      input
      steps) →
  Exact.ExactBudgetAcceptingRun
    input
    steps
cookSatisfiableToExactBudgetRun
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps
    cookSat
    with
      Bridge.cookSatisfiableGivesCNFWitness
        cnf
        cookSat
... | bits , accepted =
  Exact.guardedSATToExactRun
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps
    guardedSat
  where
    cnf =
      GlobalCNF.globalCookLevinCNF
        stateCoverage
        symbolCoverage
        nonempty
        steps
        (Guard.guardedInitialCols input steps)
        (Sound.guardedInitialBits
          stateCoverage
          symbolCoverage
          input
          steps)

    guardedSat :
      Exact.GuardedCookLevinSAT
        stateCoverage
        symbolCoverage
        nonempty
        input
        steps
    guardedSat =
      record
        { Exact.assignment = bits
        ; Exact.satisfies = accepted
        }

------------------------------------------------------------------------
-- Exact accepting run -> Cook satisfiability.
------------------------------------------------------------------------

exactBudgetRunToCookSatisfiable :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Exact.ExactBudgetAcceptingRun
    input
    steps →
  Cook.Satisfiable
    (guardedCookFormula
      stateCoverage
      symbolCoverage
      nonempty
      input
      steps)
exactBudgetRunToCookSatisfiable
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps
    exactRun
    with
      Exact.exactRunToGuardedSAT
        stateCoverage
        symbolCoverage
        nonempty
        input
        steps
        exactRun
... | guardedSat =
  Bridge.cnfWitnessGivesCookSatisfiable
    cnf
    (Exact.assignment guardedSat)
    (Exact.satisfies guardedSat)
  where
    cnf =
      GlobalCNF.globalCookLevinCNF
        stateCoverage
        symbolCoverage
        nonempty
        steps
        (Guard.guardedInitialCols input steps)
        (Sound.guardedInitialBits
          stateCoverage
          symbolCoverage
          input
          steps)

------------------------------------------------------------------------
-- Exact bridge package.
------------------------------------------------------------------------

record CookFormulaExactBudgetIff
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  constructor cook-formula-exact-budget-iff
  field
    cookSATToRun :
      Cook.Satisfiable
        (guardedCookFormula
          stateCoverage
          symbolCoverage
          nonempty
          input
          steps) →
      Exact.ExactBudgetAcceptingRun
        input
        steps

    runToCookSAT :
      Exact.ExactBudgetAcceptingRun
        input
        steps →
      Cook.Satisfiable
        (guardedCookFormula
          stateCoverage
          symbolCoverage
          nonempty
          input
          steps)

open CookFormulaExactBudgetIff public

cookFormulaExactBudgetIff :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  CookFormulaExactBudgetIff
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps
cookFormulaExactBudgetIff
    stateCoverage
    symbolCoverage
    nonempty
    input
    steps =
  cook-formula-exact-budget-iff
    (cookSatisfiableToExactBudgetRun
      stateCoverage
      symbolCoverage
      nonempty
      input
      steps)
    (exactBudgetRunToCookSatisfiable
      stateCoverage
      symbolCoverage
      nonempty
      input
      steps)

------------------------------------------------------------------------
-- Research consequence.
--
-- The concrete machine layer now supplies a literal Clay-carrier formula:
--
--   machine + input + exact step budget
--      -> Cook.BooleanFormula
--
-- with exact accepting-run semantics.
--
-- The live self-diagonal obstacle is no longer "we lack a real Cook--Levin
-- formula".  It is the resource-bounded fixed-point equation:
--
--   input = code(guardedCookFormula machine input steps)
--
-- together with a budget/quotient mechanism that avoids expanding the full
-- self-evaluation tableau.
------------------------------------------------------------------------
