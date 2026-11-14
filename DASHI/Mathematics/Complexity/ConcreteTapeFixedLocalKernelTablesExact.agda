module DASHI.Mathematics.Complexity.ConcreteTapeFixedLocalKernelTablesExact where

------------------------------------------------------------------------
-- ACTUAL COOK LOCAL KERNELS AS FINITE DECISION TABLES
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.FixedWidthPredicateDecisionTableExact as Frozen
import DASHI.Mathematics.Complexity.CNFStreamingSeekExact as Seek
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

transitionKernelTable :
  ∀ {machine : Local.ConcreteTapeMachine} →
  Canonical.EnumerationCoverage (Local.finiteState machine) →
  Canonical.EnumerationCoverage (Local.finiteSymbol machine) →
  Selector.NonemptyRuleTable machine →
  List (Frozen.DecisionRow (Selected.TransitionLocalWidth machine))
transitionKernelTable stateCoverage symbolCoverage nonempty =
  Frozen.freezePredicate
    (Selected.selectedRuleWindowPredicateWithCoverage
      stateCoverage symbolCoverage nonempty)

acceptanceKernelTable :
  ∀ {machine : Local.ConcreteTapeMachine} →
  Canonical.EnumerationCoverage (Local.finiteState machine) →
  Canonical.EnumerationCoverage (Local.finiteSymbol machine) →
  List (Frozen.DecisionRow (Endpoint.AcceptanceLocalWidth machine))
acceptanceKernelTable stateCoverage symbolCoverage =
  Frozen.freezePredicate
    (Endpoint.witnessAcceptingPredicate stateCoverage symbolCoverage)

transitionKernelFrozenSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (index : Nat) →
  Frozen.seekFrozenRejectedRows
    (transitionKernelTable stateCoverage symbolCoverage nonempty)
    index
  ≡
  Seek.seekRejectedRows
    (Selected.selectedRuleWindowPredicateWithCoverage
      stateCoverage symbolCoverage nonempty)
    (CNF.allBits (Selected.TransitionLocalWidth machine))
    index
transitionKernelFrozenSeekExact
    stateCoverage symbolCoverage nonempty index =
  Frozen.seekFrozenPredicateExact
    (Selected.selectedRuleWindowPredicateWithCoverage
      stateCoverage symbolCoverage nonempty)
    index

acceptanceKernelFrozenSeekExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (index : Nat) →
  Frozen.seekFrozenRejectedRows
    (acceptanceKernelTable stateCoverage symbolCoverage)
    index
  ≡
  Seek.seekRejectedRows
    (Endpoint.witnessAcceptingPredicate stateCoverage symbolCoverage)
    (CNF.allBits (Endpoint.AcceptanceLocalWidth machine))
    index
acceptanceKernelFrozenSeekExact
    stateCoverage symbolCoverage index =
  Frozen.seekFrozenPredicateExact
    (Endpoint.witnessAcceptingPredicate stateCoverage symbolCoverage)
    index

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The two function-valued local kernels used by the global Cook stream now have
-- same-object finite data representatives.  For the fixed self-target these
-- tables are compile-time constants.  Runtime clause generation can therefore
-- be phrased using finite coordinate code + finite row/Bool tables + natural
-- index arithmetic only.
------------------------------------------------------------------------
