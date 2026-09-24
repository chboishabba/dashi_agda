module DASHI.Mathematics.Complexity.PNotEqualsNPStrictRepresentativeDynamicClosureExact where

------------------------------------------------------------------------
-- STRICT SEMANTIC REPRESENTATIVES + FINITE QUOTIENT DP
--
-- Compose:
--
--   PNotEqualsNPStrictSemanticRepresentativeQuotientExact
--   PNotEqualsNPRestrictionQuotientDynamicProgrammingExact
--
-- For each quotient state q, use:
--
--   terminalTruth(q) := D(representative(q)).
--
-- Every representative is strictly smaller than the root Cook formula.
--
-- The dynamic-program theorem then computes the exact root decision from the
-- finite depth-by-state recurrence.  Therefore the root can be evaluated using
-- only strictly smaller D-queries, with at most one semantic query per state
-- if those state values are memoized.
--
-- This is the first theorem in the route that genuinely removes SAME-SIZE
-- calls to the hypothetical SAT decider.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_<_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact as DP
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict

------------------------------------------------------------------------
-- Terminal labels from strictly smaller representatives.
------------------------------------------------------------------------

strictRepresentativeTerminalLabels :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient root) →
  DP.TerminalStateLabelling
    (Strict.quotient strictQuotient)
    (Bridge.indexedOracleFromCookInP satP)
strictRepresentativeTerminalLabels
    satP
    strictQuotient =
  DP.terminal-state-labelling
    terminalTruth
    terminalCorrect
  where
    quotient :
      Quotient.RestrictionSemanticQuotient root
    quotient =
      Strict.quotient strictQuotient

    terminalTruth :
      Fin (Quotient.stateCount quotient) →
      Bool
    terminalTruth state =
      PR.decide satP
        (Strict.representative
          strictQuotient
          state)

    terminalCorrect :
      ∀ {terminal : SAT.BooleanFormula 0}
        (derivation :
          Family.RestrictionDerivation
            root
            terminal) →
      terminalTruth
        (Quotient.classify
          quotient
          derivation)
      ≡
      PR.decide satP
        (Bridge.indexedToCook terminal)
    terminalCorrect derivation =
      symmetry
        (Strict.representativeDecisionEqualsReachableDecision
          satP
          strictQuotient
          derivation)
      where
        symmetry :
          ∀ {A : Set}
            {left right : A} →
          left ≡ right →
          right ≡ left
        symmetry equality =
          Relation.Binary.PropositionalEquality.sym equality

------------------------------------------------------------------------
-- Root decision from the finite state DP.
------------------------------------------------------------------------

strictRepresentativeDPComputesRoot :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (satP : PR.InP cost Clay.SATLanguage)
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient root) →
  DP.quotientTruthAtDepth
    (Strict.quotient strictQuotient)
    (strictRepresentativeTerminalLabels
      satP
      strictQuotient)
    rootVariables
    (Quotient.classify
      (Strict.quotient strictQuotient)
      Family.restrictionRoot)
  ≡
  PR.decide satP
    (Bridge.indexedToCook root)
strictRepresentativeDPComputesRoot
    satP
    strictQuotient =
  DP.quotientTruthComputesRootDecision
    (Strict.quotient strictQuotient)
    (Bridge.indexedOracleFromCookInP satP)
    (strictRepresentativeTerminalLabels
      satP
      strictQuotient)

------------------------------------------------------------------------
-- Every semantic query supplying the DP state table is strictly smaller than
-- the root formula.
------------------------------------------------------------------------

everyStateRepresentativeStrictlySmaller :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (strictQuotient :
      Strict.StrictSemanticRepresentativeQuotient root)
    (state :
      Fin
        (Quotient.stateCount
          (Strict.quotient strictQuotient))) →
  Size.formulaNodeCount
    (Strict.representative
      strictQuotient
      state)
  <
  Size.formulaNodeCount
    (Bridge.indexedToCook root)
everyStateRepresentativeStrictlySmaller
    strictQuotient state =
  Strict.representativeStrictlySmallerThanRoot
    strictQuotient
    state

------------------------------------------------------------------------
-- With memoization, one D-query per quotient state suffices to fill all state
-- truth values used by the recurrence.
------------------------------------------------------------------------

strictRepresentativeQueryCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Strict.StrictSemanticRepresentativeQuotient root →
  Nat
strictRepresentativeQueryCount strictQuotient =
  Quotient.stateCount
    (Strict.quotient strictQuotient)

------------------------------------------------------------------------
-- Research consequence.
--
-- The route now has a concrete non-circular target stronger than a small
-- quotient image:
--
--   quotient state
--      -> strictly smaller equisatisfiable representative.
--
-- If such representatives are constructible for the pre-fixed-point
-- self-diagonal family, the exact root SAT bit follows from finitely many
-- strictly smaller D calls plus the depth-state Shannon DP.
--
-- What remains OPEN:
--
--   * construct the quotient and strict representatives from the special
--     self-instantiation structure;
--   * prove their construction cost and represented DP fit the self-size
--     budget;
--   * use the resulting smaller-query evaluator inside the bounded fixed-point
--     construction.
------------------------------------------------------------------------
