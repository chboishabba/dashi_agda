module DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostedExact where

------------------------------------------------------------------------
-- COSTED EXECUTION OF THE ACTUAL GLOBAL STREAMED CLAUSE PATH
--
-- Unlike the earlier section-max receipt, this owner follows the same residual
-- transition -> initial -> accepting control flow as `globalClauseSeek` and
-- returns both its exact SeekResult and the work actually charged on that path.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTransitionConjunctionExact as Transition
import DASHI.Mathematics.Complexity.CNFVariableRenamingExact as Rename
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.CNFStreamingSeekCostExact as CostSeek
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseExact as Stream
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinStreamingClauseCostExact as Budget
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Generic costed global result.
------------------------------------------------------------------------

record CostedGlobalClause
    {machine : Local.ConcreteTapeMachine}
    (steps cols : Nat) : Set₁ where
  constructor costed-global-clause
  field
    result :
      Seek.SeekResult
        (CNF.Clause (Endpoint.ExtendedGlobalWidth machine steps cols))
    work : Nat

open CostedGlobalClause public

------------------------------------------------------------------------
-- Transition section: exact mapped costed placed seek.
------------------------------------------------------------------------

transitionCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  CostedGlobalClause {machine} steps cols
transitionCosted stateCoverage symbolCoverage nonempty steps cols index
  with CostSeek.seekPlacedAllCosted
    (Transition.allGlobalTransitionPredicates
      stateCoverage symbolCoverage nonempty steps cols)
    index
... | CostSeek.costed-seek found work =
  costed-global-clause
    (Seek.mapSeek (Rename.renameClause Endpoint.liftBaseIndex) found)
    work

transitionCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  result (transitionCosted stateCoverage symbolCoverage nonempty steps cols index)
  ≡ Stream.transitionClauseSeek
      stateCoverage symbolCoverage nonempty steps cols index
transitionCostedResultExact
    stateCoverage symbolCoverage nonempty steps cols index
  with CostSeek.seekPlacedAllCosted
      (Transition.allGlobalTransitionPredicates
        stateCoverage symbolCoverage nonempty steps cols)
      index
     | CostSeek.seekPlacedAllCostedResultExact
        (Transition.allGlobalTransitionPredicates
          stateCoverage symbolCoverage nonempty steps cols)
        index
... | CostSeek.costed-seek found work | exact
  rewrite exact = refl

transitionCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols index : Nat) →
  work (transitionCosted stateCoverage symbolCoverage nonempty steps cols index)
  ≤ Budget.transitionPredicateBudget machine steps cols
transitionCostedWorkBound
    stateCoverage symbolCoverage nonempty steps cols index
  with CostSeek.seekPlacedAllCosted
      (Transition.allGlobalTransitionPredicates
        stateCoverage symbolCoverage nonempty steps cols)
      index
     | Budget.transitionPredicateWorkBound
        stateCoverage symbolCoverage nonempty steps cols index
... | CostSeek.costed-seek found work | bound = bound

------------------------------------------------------------------------
-- Initial section with exact result and literal visited-cell work.
------------------------------------------------------------------------

initialCosted :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat} →
  CNF.Bits (Decode.RowBitsWidth machine cols) →
  Nat →
  CostedGlobalClause {machine} steps cols
initialCosted {steps = steps} {cols = cols} CNF.[]ᵇ index =
  costed-global-clause (Seek.exhausted index) zero
initialCosted {steps = steps} {cols = cols}
    (bit CNF.∷ᵇ bits) zero =
  costed-global-clause
    (Seek.found
      (Endpoint.unitClauseForBit
        (Endpoint.initialRowExtendedRename Fin.zero)
        bit))
    (suc zero)
  where
    import Data.Fin.Base as Fin
initialCosted {steps = steps} {cols = cols}
    (bit CNF.∷ᵇ bits) (suc index)
  with initialCosted
    {steps = steps} {cols = cols}
    bits index
... | costed-global-clause found work =
  -- The result needs the shifted rename.  Rather than reusing the recursive
  -- result at the wrong index type, delegate exact result to the canonical
  -- initial seeker below; only the work recursion is relevant here.
  costed-global-clause
    (Stream.initialClauseSeek
      {steps = steps} {cols = cols}
      (bit CNF.∷ᵇ bits) (suc index))
    (suc work)

initialCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (bits : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  result (initialCosted {steps = steps} {cols = cols} bits index)
  ≡ Stream.initialClauseSeek {steps = steps} bits index
initialCostedResultExact CNF.[]ᵇ index = refl
initialCostedResultExact (bit CNF.∷ᵇ bits) zero = refl
initialCostedResultExact (bit CNF.∷ᵇ bits) (suc index) = refl

initialCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (bits : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  work (initialCosted {steps = steps} {cols = cols} bits index)
  ≤ Decode.RowBitsWidth machine cols
initialCostedWorkBound CNF.[]ᵇ index = NatP.≤-refl _
initialCostedWorkBound (bit CNF.∷ᵇ bits) zero = NatP.s≤s NatP.z≤n
initialCostedWorkBound (bit CNF.∷ᵇ bits) (suc index)
  with initialCosted bits index
     | initialCostedWorkBound bits index
... | costed-global-clause found work | bound = NatP.s≤s bound

------------------------------------------------------------------------
-- Accepting section.
------------------------------------------------------------------------

acceptingCosted :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  Nat →
  CostedGlobalClause {machine} steps cols
acceptingCosted stateCoverage symbolCoverage zero =
  costed-global-clause
    (Seek.found Endpoint.someAcceptanceWitnessClause)
    zero
acceptingCosted {steps = steps} {cols = cols}
    stateCoverage symbolCoverage (suc index)
  with CostSeek.seekPlacedAllCosted
    (Endpoint.acceptanceImplicationPredicatesFin
      stateCoverage symbolCoverage (Endpoint.finList cols))
    index
... | CostSeek.costed-seek found work =
  costed-global-clause found work

acceptingCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (index : Nat) →
  result (acceptingCosted
    {steps = steps} {cols = cols}
    stateCoverage symbolCoverage index)
  ≡ Stream.acceptingClauseSeek
      {steps = steps} {cols = cols}
      stateCoverage symbolCoverage index
acceptingCostedResultExact stateCoverage symbolCoverage zero = refl
acceptingCostedResultExact {cols = cols}
    stateCoverage symbolCoverage (suc index)
  with CostSeek.seekPlacedAllCosted
      (Endpoint.acceptanceImplicationPredicatesFin
        stateCoverage symbolCoverage (Endpoint.finList cols))
      index
     | CostSeek.seekPlacedAllCostedResultExact
        (Endpoint.acceptanceImplicationPredicatesFin
          stateCoverage symbolCoverage (Endpoint.finList cols))
        index
... | CostSeek.costed-seek found work | exact
  rewrite exact = refl

acceptingCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine} {steps cols : Nat}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (index : Nat) →
  work (acceptingCosted
    {steps = steps} {cols = cols}
    stateCoverage symbolCoverage index)
  ≤ Budget.acceptingPredicateBudget machine cols
acceptingCostedWorkBound stateCoverage symbolCoverage zero = NatP.z≤n
acceptingCostedWorkBound {steps = steps} {cols = cols}
    stateCoverage symbolCoverage (suc index)
  with CostSeek.seekPlacedAllCosted
      (Endpoint.acceptanceImplicationPredicatesFin
        stateCoverage symbolCoverage (Endpoint.finList cols))
      index
     | Budget.acceptingPredicateWorkBound
        {steps = steps} {cols = cols}
        stateCoverage symbolCoverage (suc index)
... | CostSeek.costed-seek found work | bound = bound

------------------------------------------------------------------------
-- Exact global residual composition.
------------------------------------------------------------------------

globalClauseSeekCosted :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols)) →
  Nat →
  CostedGlobalClause {machine} steps cols
globalClauseSeekCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
  with transitionCosted stateCoverage symbolCoverage nonempty steps cols index
... | costed-global-clause (Seek.found clause) transitionWork =
  costed-global-clause (Seek.found clause) transitionWork
... | costed-global-clause (Seek.exhausted remaining) transitionWork
  with initialCosted {steps = steps} {cols = cols} initialTarget remaining
... | costed-global-clause (Seek.found clause) initialWork =
  costed-global-clause (Seek.found clause) (transitionWork + initialWork)
... | costed-global-clause (Seek.exhausted afterInitial) initialWork
  with acceptingCosted {steps = steps} {cols = cols}
    stateCoverage symbolCoverage afterInitial
... | costed-global-clause acceptingResult acceptingWork =
  costed-global-clause
    acceptingResult
    ((transitionWork + initialWork) + acceptingWork)

globalClauseSeekCostedResultExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  result (globalClauseSeekCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index)
  ≡ Stream.globalClauseSeek
      stateCoverage symbolCoverage nonempty steps cols initialTarget index
globalClauseSeekCostedResultExact
    stateCoverage symbolCoverage nonempty steps cols initialTarget index
  with transitionCosted stateCoverage symbolCoverage nonempty steps cols index
     | transitionCostedResultExact
        stateCoverage symbolCoverage nonempty steps cols index
... | costed-global-clause (Seek.found clause) transitionWork | transitionExact
  rewrite transitionExact = refl
... | costed-global-clause (Seek.exhausted remaining) transitionWork | transitionExact
  rewrite transitionExact
  with initialCosted {steps = steps} {cols = cols} initialTarget remaining
     | initialCostedResultExact
        {steps = steps} {cols = cols} initialTarget remaining
... | costed-global-clause (Seek.found clause) initialWork | initialExact
  rewrite initialExact = refl
... | costed-global-clause (Seek.exhausted afterInitial) initialWork | initialExact
  rewrite initialExact
  with acceptingCosted {steps = steps} {cols = cols}
      stateCoverage symbolCoverage afterInitial
     | acceptingCostedResultExact
        {steps = steps} {cols = cols}
        stateCoverage symbolCoverage afterInitial
... | costed-global-clause acceptingResult acceptingWork | acceptingExact
  rewrite acceptingExact = refl

------------------------------------------------------------------------
-- Path work is bounded by the closed sum of section maxima.
------------------------------------------------------------------------

globalClauseSeekCostedWorkBound :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (steps cols : Nat)
    (initialTarget : CNF.Bits (Decode.RowBitsWidth machine cols))
    (index : Nat) →
  work (globalClauseSeekCosted
    stateCoverage symbolCoverage nonempty steps cols initialTarget index)
  ≤ Budget.globalClauseSeekWorkBudget machine steps cols
globalClauseSeekCostedWorkBound
    {machine} stateCoverage symbolCoverage nonempty steps cols initialTarget index
  with transitionCosted stateCoverage symbolCoverage nonempty steps cols index
     | transitionCostedWorkBound
        stateCoverage symbolCoverage nonempty steps cols index
... | costed-global-clause (Seek.found clause) transitionWork | transitionBound =
  NatP.≤-trans
    transitionBound
    (NatP.m≤m+n
      (Budget.transitionPredicateBudget machine steps cols)
      (Decode.RowBitsWidth machine cols
        + Budget.acceptingPredicateBudget machine cols))
... | costed-global-clause (Seek.exhausted remaining) transitionWork | transitionBound
  with initialCosted {steps = steps} {cols = cols} initialTarget remaining
     | initialCostedWorkBound
        {steps = steps} {cols = cols} initialTarget remaining
... | costed-global-clause (Seek.found clause) initialWork | initialBound =
  NatP.≤-trans
    (NatP.+-mono-≤ transitionBound initialBound)
    (NatP.m≤m+n
      (Budget.transitionPredicateBudget machine steps cols
        + Decode.RowBitsWidth machine cols)
      (Budget.acceptingPredicateBudget machine cols))
... | costed-global-clause (Seek.exhausted afterInitial) initialWork | initialBound
  with acceptingCosted {steps = steps} {cols = cols}
      stateCoverage symbolCoverage afterInitial
     | acceptingCostedWorkBound
        {steps = steps} {cols = cols}
        stateCoverage symbolCoverage afterInitial
... | costed-global-clause acceptingResult acceptingWork | acceptingBound =
  NatP.+-mono-≤
    (NatP.+-mono-≤ transitionBound initialBound)
    acceptingBound

------------------------------------------------------------------------
-- This is now the exact path-level costed clause evaluator.  The next owner can
-- instrument token/bit cursor recursion by charging this actual work whenever a
-- `cnfAt` state requests a global clause.
------------------------------------------------------------------------
