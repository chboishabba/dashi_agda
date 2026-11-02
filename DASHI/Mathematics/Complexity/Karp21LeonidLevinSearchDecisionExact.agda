module DASHI.Mathematics.Complexity.Karp21LeonidLevinSearchDecisionExact where

------------------------------------------------------------------------
-- LEONID LEVIN (1973) SEARCH-VS-DECISION, ON THE ACTUAL COOK WORD.
--
-- Historical roots, with distinct ownership:
--   Stephen A. Cook, "The complexity of theorem-proving procedures",
--     STOC 1971, DOI 10.1145/800157.805047.
--   Leonid A. Levin, "Universal Sequential Search Problems",
--     Problemy Peredachi Informatsii 9(3) (1973), 115-116;
--     English translation: Problems of Information Transmission
--     9(3) (1973), 265-266. Math-Net.Ru: ppi914.
--   Richard M. Karp, "Reducibility Among Combinatorial Problems",
--     1972, DOI 10.1007/978-1-4684-2001-2_9.
--
-- Cook's Boolean AST, strict bitword parser and concrete-tape
-- accepting-run equivalence are reused from the prior DASHI owners.
-- Levin's SEARCH framing asks for an actual witness, not merely a
-- decision Boolean. This file proves exact mutual translations for
-- the SAME serialized Cook formula and for the SAME Karp N21 graph.
--
-- Important NON-PROMOTION:
-- * Cook.Assignment is Nat -> Bool, NOT a finitely encoded witness.
-- * There is no polynomial checker or length bound in this module.
-- * This is not a Leonid Levin universal-search scheduler, Kt
--   optimality, SAT InNP, or any NP-completeness theorem.
-- * Michael Levin (biology) is entirely separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact as SAT
import DASHI.Mathematics.Complexity.Karp21CookLevinConcreteBitWordReuseExact as K00
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Tape
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Rules
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Runs
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointConsistencySoundExact as Sparse

------------------------------------------------------------------------
-- Leonid-style relation: a search solution contains a parsed FORMULA
-- and an actual assignment that the source-owned evaluator accepts.
-- It is indexed by exactly the SAME canonical List Bool SAT word.
------------------------------------------------------------------------

StrictCookSearchWitness : Word.BitWord → Set
StrictCookSearchWitness word =
  Σ Cook.BooleanFormula (λ formula →
    (Strict.strictDecodeCookFormulaBits word ≡ just formula)
    × Σ Cook.Assignment
        (λ assignment → Cook.evaluate formula assignment ≡ true))

-- Destructure Cook's actual Satisfiable constructor. Do not assume
-- that its record projections have been opened at top level.
cookSatisfyingAssignmentToSearch :
  (formula : Cook.BooleanFormula) →
  Cook.Satisfiable formula →
  Σ Cook.Assignment
    (λ assignment → Cook.evaluate formula assignment ≡ true)
cookSatisfyingAssignmentToSearch formula
  (Cook.satisfyingAssignment assignment verified) =
  assignment , verified

strictCookDecisionToSearch :
  (word : Word.BitWord) →
  PR.accepts SAT.strictSATLanguage word →
  StrictCookSearchWitness word
strictCookDecisionToSearch word accepted
  with Strict.strictDecodeCookFormulaBits word
... | nothing = ⊥-elim accepted
... | just formula =
  formula , (refl , cookSatisfyingAssignmentToSearch formula accepted)

strictCookSearchToDecision :
  (word : Word.BitWord) →
  StrictCookSearchWitness word →
  PR.accepts SAT.strictSATLanguage word
strictCookSearchToDecision word (formula , (parsed , (assignment , valid)))
  rewrite parsed = Cook.satisfyingAssignment assignment valid

strictCookSearchDecisionIff :
  (word : Word.BitWord) →
  PR.Iff (PR.accepts SAT.strictSATLanguage word)
    (StrictCookSearchWitness word)
strictCookSearchDecisionIff word =
  PR.iff (strictCookDecisionToSearch word)
         (strictCookSearchToDecision word)

------------------------------------------------------------------------
-- Actual concrete Cook-Levin instance, NOT a hypothetical simulator.
-- Both maps retain one machine, input, and exact step budget.
------------------------------------------------------------------------

concreteRunToStrictCookSearch :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Runs.ExactBudgetAcceptingRun input steps →
  StrictCookSearchWitness
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
concreteRunToStrictCookSearch states symbols nonempty input steps run =
  strictCookDecisionToSearch
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
    (K00.exactRunToStrictCookSATWordAcceptance
      states symbols nonempty input steps run)

strictCookSearchToConcreteRun :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  StrictCookSearchWitness
    (K00.guardedCookLevinBitWord states symbols nonempty input steps) →
  Runs.ExactBudgetAcceptingRun input steps
strictCookSearchToConcreteRun states symbols nonempty input steps search =
  K00.strictCookSATWordAcceptanceToRun
    states symbols nonempty input steps
    (strictCookSearchToDecision
      (K00.guardedCookLevinBitWord states symbols nonempty input steps)
      search)

concreteRunStrictCookSearchIff :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Canonical.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Canonical.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  PR.Iff (Runs.ExactBudgetAcceptingRun input steps)
    (StrictCookSearchWitness
      (K00.guardedCookLevinBitWord states symbols nonempty input steps))
concreteRunStrictCookSearchIff states symbols nonempty input steps =
  PR.iff
    (concreteRunToStrictCookSearch states symbols nonempty input steps)
    (strictCookSearchToConcreteRun states symbols nonempty input steps)

------------------------------------------------------------------------
-- Same search/decision distinction on the actual signed Karp N21
-- graph with a REAL 2m-bit sparse endpoint certificate verifier.
-- An empty or enormous declared vertex set does not change its
-- witness representation. No polynomial graph-word parser is assumed.
------------------------------------------------------------------------

n21DecisionToSparseSearch :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  Cut.WeightedMaxCutYES graph →
  Sparse.SparseBitWordYES graph
n21DecisionToSparseSearch graph =
  PR.forward (Sparse.n21SparseBitWordDecisionIff graph)

n21SparseSearchToDecision :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  Sparse.SparseBitWordYES graph →
  Cut.WeightedMaxCutYES graph
n21SparseSearchToDecision graph =
  PR.backward (Sparse.n21SparseBitWordDecisionIff graph)

n21SameGraphSearchDecisionIff :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  PR.Iff (Cut.WeightedMaxCutYES graph) (Sparse.SparseBitWordYES graph)
n21SameGraphSearchDecisionIff graph =
  PR.iff (n21DecisionToSparseSearch graph)
         (n21SparseSearchToDecision graph)
