module DASHI.Mathematics.Complexity.ConcreteTapeCookLevinPrizeFacingExact where

------------------------------------------------------------------------
-- PRIZE-FACING COOK--LEVIN CERTIFICATE
--
-- This file intentionally stops at the standard-theory min-cut:
--
-- * exact-budget satisfiability iff an actual accepting run;
-- * exact variable count;
-- * closed polynomial clause bound.
--
-- No new generic complexity framework is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Selector
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeSATToAcceptingRunExact as Sound
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeExact as Size
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinSizeClosedExact as Closed
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalCookLevinCNFExact as GlobalCNF
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.ConcreteTapeFixedDimensionDecodeExact as Decode
import DASHI.Mathematics.Complexity.ConcreteTapeSelectedRuleWindowCNFExact as Selected
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

record PrizeFacingCookLevinCertificate
    {machine : Local.ConcreteTapeMachine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) : Set₁ where
  field
    exactBudgetSemantics :
      Exact.CookLevinExactBudgetIff
        stateCoverage symbolCoverage nonempty input steps

    exactVariableCount :
      Endpoint.ExtendedGlobalWidth
        machine steps (Guard.guardedInitialCols input steps)
      ≡
      ((Agda.Builtin.Nat.suc steps) *
          (Guard.guardedInitialCols input steps *
            Canonical.CellWidth machine))
      +
      (steps * Selector.RuleWidth machine)
      +
      Guard.guardedInitialCols input steps

    closedClauseBound :
      Σ Nat (λ slack →
        Size.listLength
          (GlobalCNF.globalCookLevinCNF
            stateCoverage symbolCoverage nonempty
            steps (Guard.guardedInitialCols input steps)
            (Sound.guardedInitialBits
              stateCoverage symbolCoverage input steps))
        + slack
        ≡
          ((steps * (Guard.guardedInitialCols input steps Data.Nat.∸ 2))
            * (2 Agda.Builtin.Nat.^ Selected.TransitionLocalWidth machine))
          +
          Decode.RowBitsWidth machine
            (Guard.guardedInitialCols input steps)
          +
          Agda.Builtin.Nat.suc
            (Guard.guardedInitialCols input steps *
              (2 Agda.Builtin.Nat.^ Endpoint.AcceptanceLocalWidth machine)))

open PrizeFacingCookLevinCertificate public

prizeFacingCookLevinCertificate :
  ∀ {machine}
    (stateCoverage :
      Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage :
      Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (nonempty : Selector.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  PrizeFacingCookLevinCertificate
    stateCoverage symbolCoverage nonempty input steps
prizeFacingCookLevinCertificate
    stateCoverage symbolCoverage nonempty input steps = record
  { exactBudgetSemantics =
      Exact.cookLevinExactBudgetIff
        stateCoverage symbolCoverage nonempty input steps
  ; exactVariableCount =
      Size.extendedGlobalWidth_exact
        machine steps (Guard.guardedInitialCols input steps)
  ; closedClauseBound =
      Closed.globalCookLevinClause_bound
        stateCoverage symbolCoverage nonempty
        steps (Guard.guardedInitialCols input steps)
        (Sound.guardedInitialBits
          stateCoverage symbolCoverage input steps)
  }
