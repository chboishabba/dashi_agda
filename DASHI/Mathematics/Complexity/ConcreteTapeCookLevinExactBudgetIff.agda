module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff where

------------------------------------------------------------------------
-- PRIZE-FACING COOK--LEVIN SAME-OBJECT CAPSTONE
--
-- For one concrete machine, literal input, and exact time budget T:
--
--   the guarded global Cook--Levin CNF is satisfiable
--        iff
--   there is an actual accepting WellFormedTapeRun of exactly T transitions.
--
-- This is the language-preservation theorem needed by the reduction.  It does
-- not attempt to formalize a new general complexity framework.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeFlatAssignmentExact as Flat
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunGlobalCompleteExact as Complete
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunAssignmentExact as Assignment
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

guardedInitialCanonicalCellCount :
  ∀ {machine}
    (input : Input.InputWord machine)
    (steps : Nat) →
  Canonical.listLength
    (Local.cells (Guard.guardedInitialRow input steps))
  ≡ Guard.guardedInitialCols input steps
guardedInitialCanonicalCellCount input steps =
  trans
    (Assignment.canonicalLength_eq_coordinateLength
      (Local.cells (Guard.guardedInitialRow input steps)))
    (Guard.guardedInitialCellCount input steps)

record GuardedCookLevinSAT
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set where
  field
    assignment :
      CNF.Bits
        (Endpoint.ExtendedGlobalWidth machine steps
          (Guard.guardedInitialCols input steps))
    satisfies :
      CNF.evaluateCNF
        (GlobalCNF.globalCookLevinCNF
          stateCoverage symbolCoverage nonempty
          steps (Guard.guardedInitialCols input steps)
          (Sound.guardedInitialBits
            stateCoverage symbolCoverage input steps))
        assignment
      ≡ Agda.Builtin.Bool.true

open GuardedCookLevinSAT public

record ExactBudgetAcceptingRun
    {machine : Local.ConcreteTapeMachine}
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    rows : Agda.Builtin.List.List (Local.TapeRow machine)
    finish : Local.TapeRow machine
    certificate :
      Accepting.AcceptingWellFormedRun
        machine
        (Guard.guardedInitialRow input steps)
        rows finish
    exactLength :
      Accepting.acceptingRunLength certificate ≡ steps

open ExactBudgetAcceptingRun public

guardedSATToExactRun :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  GuardedCookLevinSAT
    stateCoverage symbolCoverage nonempty input steps →
  ExactBudgetAcceptingRun input steps
guardedSATToExactRun
    stateCoverage symbolCoverage nonempty input steps sat
    with Sound.satisfyingCookLevinAssignmentToAcceptingRun
      stateCoverage symbolCoverage nonempty input steps
      (assignment sat) (satisfies sat)
... | decoded =
  record
    { rows = Sound.rows decoded
    ; finish = Sound.finish decoded
    ; certificate = Sound.certificate decoded
    ; exactLength = Sound.exactLength decoded
    }

exactRunToGuardedSAT :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  ExactBudgetAcceptingRun input steps →
  GuardedCookLevinSAT
    stateCoverage symbolCoverage nonempty input steps
exactRunToGuardedSAT
    stateCoverage symbolCoverage nonempty input steps exact
    with exactLength exact
       | guardedInitialCanonicalCellCount input steps
... | refl | refl =
  record
    { assignment =
        Assignment.encodeAcceptingRunAssignment
          stateCoverage symbolCoverage (certificate exact)
    ; satisfies =
        targetRewrite
          (Complete.acceptingRunSatisfiesGlobalCookLevinCNF
            stateCoverage symbolCoverage nonempty
            (certificate exact))
    }
  where
    targetRewrite :
      CNF.evaluateCNF
        (GlobalCNF.globalCookLevinCNF
          stateCoverage symbolCoverage nonempty
          steps (Guard.guardedInitialCols input steps)
          (Flat.encodeRow stateCoverage symbolCoverage
            (Guard.guardedInitialRow input steps)))
        (Assignment.encodeAcceptingRunAssignment
          stateCoverage symbolCoverage (certificate exact))
      ≡ Agda.Builtin.Bool.true →
      CNF.evaluateCNF
        (GlobalCNF.globalCookLevinCNF
          stateCoverage symbolCoverage nonempty
          steps (Guard.guardedInitialCols input steps)
          (Sound.guardedInitialBits
            stateCoverage symbolCoverage input steps))
        (Assignment.encodeAcceptingRunAssignment
          stateCoverage symbolCoverage (certificate exact))
      ≡ Agda.Builtin.Bool.true
    targetRewrite proof
      rewrite Sound.guardedInitialBitsDecode
        stateCoverage symbolCoverage input steps =
      proof

record CookLevinExactBudgetIff
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    satToRun :
      GuardedCookLevinSAT
        stateCoverage symbolCoverage nonempty input steps →
      ExactBudgetAcceptingRun input steps
    runToSat :
      ExactBudgetAcceptingRun input steps →
      GuardedCookLevinSAT
        stateCoverage symbolCoverage nonempty input steps

cookLevinExactBudgetIff :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  CookLevinExactBudgetIff
    stateCoverage symbolCoverage nonempty input steps
cookLevinExactBudgetIff
    stateCoverage symbolCoverage nonempty input steps = record
  { satToRun =
      guardedSATToExactRun
        stateCoverage symbolCoverage nonempty input steps
  ; runToSat =
      exactRunToGuardedSAT
        stateCoverage symbolCoverage nonempty input steps
  }
