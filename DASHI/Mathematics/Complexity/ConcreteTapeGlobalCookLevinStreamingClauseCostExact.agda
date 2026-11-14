module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostExact where

------------------------------------------------------------------------
-- CLOSED WORK BUDGET FOR ACTUAL GLOBAL COOK--LEVIN CLAUSE SEEK
--
-- Cost currency = local predicate evaluations + initial-target cell visits.
-- This follows the same transition -> initial -> accepting residual-index route
-- as `ConcreteTapeGlobalCookLevinStreamingClauseExact.globalClauseSeek`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Data.Nat using (_∸_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.CNFStreamingSeekCostExact as CostSeek
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseExact as Stream
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as Size
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeClosedExact as Closed
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Transition section.
------------------------------------------------------------------------

transitionPredicateWork :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) → Nat
transitionPredicateWork stateCoverage symbolCoverage nonempty steps cols index =
  CostSeek.predicateWork
    (CostSeek.seekPlacedAllCosted
      (Transition.allGlobalTransitionPredicates
        stateCoverage symbolCoverage nonempty steps cols)
      index)

transitionPredicateBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat → Nat
transitionPredicateBudget machine steps cols =
  (steps * (cols ∸ 2)) * (2 ^ Selected.TransitionLocalWidth machine)

transitionPredicateWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  transitionPredicateWork
    stateCoverage symbolCoverage nonempty steps cols index
  ≤ transitionPredicateBudget machine steps cols
transitionPredicateWorkBound
    {machine} stateCoverage symbolCoverage nonempty steps cols index
  rewrite Closed.allGlobalTransitionPredicates_count
    stateCoverage symbolCoverage nonempty steps cols =
  CostSeek.seekPlacedAllWorkBound
    (Transition.allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
    index

------------------------------------------------------------------------
-- Initial endpoint section: at most one target-bit visit per residual index.
------------------------------------------------------------------------

initialSeekWork :
  ∀ {n : Nat} →
  CNF.Bits n → Nat → Nat
initialSeekWork CNF.[]ᵇ index = zero
initialSeekWork (bit CNF.∷ᵇ bits) zero = suc zero
initialSeekWork (bit CNF.∷ᵇ bits) (suc index) =
  suc (initialSeekWork bits index)

initialSeekWorkBound :
  ∀ {n : Nat}
    (bits : CNF.Bits n)
    (index : Nat) →
  initialSeekWork bits index ≤ n
initialSeekWorkBound CNF.[]ᵇ index = NatP.≤-refl _
initialSeekWorkBound (bit CNF.∷ᵇ bits) zero = NatP.s≤s NatP.z≤n
initialSeekWorkBound (bit CNF.∷ᵇ bits) (suc index) =
  NatP.s≤s (initialSeekWorkBound bits index)

------------------------------------------------------------------------
-- Accepting endpoint section.
------------------------------------------------------------------------

acceptingPredicateWork :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Nat → Nat
acceptingPredicateWork stateCoverage symbolCoverage zero = zero
acceptingPredicateWork {cols = cols}
    stateCoverage symbolCoverage (suc index) =
  CostSeek.predicateWork
    (CostSeek.seekPlacedAllCosted
      (Endpoint.acceptanceImplicationPredicatesFin
        stateCoverage symbolCoverage (Endpoint.finList cols))
      index)

acceptingPredicateBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat
acceptingPredicateBudget machine cols =
  cols * (2 ^ Endpoint.AcceptanceLocalWidth machine)

acceptingPredicateWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (index : Nat) →
  acceptingPredicateWork
    {steps = steps} {cols = cols}
    stateCoverage symbolCoverage index
  ≤ acceptingPredicateBudget machine cols
acceptingPredicateWorkBound
    {machine} {steps} {cols} stateCoverage symbolCoverage zero =
  NatP.z≤n
acceptingPredicateWorkBound
    {machine} {steps} {cols} stateCoverage symbolCoverage (suc index)
  rewrite Closed.acceptancePredicate_count
    stateCoverage symbolCoverage (Endpoint.finList cols)
      | Closed.finList_count cols =
  CostSeek.seekPlacedAllWorkBound
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage (Endpoint.finList cols))
    index

------------------------------------------------------------------------
-- Closed global budget.  We use the sum of all section maxima; residual-index
-- early exits only make the actual work smaller.
------------------------------------------------------------------------

globalClauseSeekWorkBudget :
  (machine : Local.ConcreteTapeMachine) → Nat → Nat → Nat
globalClauseSeekWorkBudget machine steps cols =
  transitionPredicateBudget machine steps cols
  + Decode.RowBitsWidth machine cols
  + acceptingPredicateBudget machine cols

record GlobalClauseSeekWorkReceipt
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) : Set where
  field
    transitionWork : Nat
    initialWork : Nat
    acceptingWork : Nat

    transitionExact :
      transitionWork
      ≡ transitionPredicateWork
          stateCoverage symbolCoverage nonempty steps cols index

    initialBound : initialWork ≤ Decode.RowBitsWidth machine cols
    acceptingBound :
      acceptingWork ≤ acceptingPredicateBudget machine cols

    totalWorkBound :
      transitionWork + initialWork + acceptingWork
      ≤ globalClauseSeekWorkBudget machine steps cols

open GlobalClauseSeekWorkReceipt public

canonicalGlobalClauseSeekWorkReceipt :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  GlobalClauseSeekWorkReceipt
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
canonicalGlobalClauseSeekWorkReceipt
    {machine} stateCoverage symbolCoverage nonempty steps cols initialTarget index =
  record
    { transitionWork = transitionPredicateWork
        stateCoverage symbolCoverage nonempty steps cols index
    ; initialWork = initialSeekWork initialTarget index
    ; acceptingWork = acceptingPredicateWork
        {steps = steps} {cols = cols}
        stateCoverage symbolCoverage index
    ; transitionExact = refl
    ; initialBound = initialSeekWorkBound initialTarget index
    ; acceptingBound = acceptingPredicateWorkBound
        {steps = steps} {cols = cols}
        stateCoverage symbolCoverage index
    ; totalWorkBound =
        NatP.+-mono-≤
          (NatP.+-mono-≤
            (transitionPredicateWorkBound
              stateCoverage symbolCoverage nonempty steps cols index)
            (initialSeekWorkBound initialTarget index))
          (acceptingPredicateWorkBound
            {steps = steps} {cols = cols}
            stateCoverage symbolCoverage index)
    }

------------------------------------------------------------------------
-- POLYNOMIAL SHAPE
--
--   transition: T*(cols-2)*2^w_trans
--   initial:    cols*CellWidth
--   accepting:  cols*2^w_accept
--
-- Both w_trans and w_accept depend only on the fixed machine.  This is the
-- closed work shape required by the universal streamed-bit compiler.  It is not
-- yet a standard-TM step count: arithmetic/index decoding and finite-control
-- compilation still need explicit constant/polynomial overhead receipts.
------------------------------------------------------------------------
