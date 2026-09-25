module DASHI.Mathematics.Complexity.PNotEqualsNPGlobalStructuralChainFirewallExact where

------------------------------------------------------------------------
-- GLOBAL STRUCTURAL-CHAIN PRODUCER FIREWALL
--
-- PNotEqualsNPClosedStrictRepresentativeQuotientExact defines a genuinely
-- non-D-labelled semantic certificate:
--
--   formula
--      -> strictly smaller equisatisfiable formula
--      -> ...
--      -> literal constant true/false.
--
-- Its terminal bit is proved to equal SAT truth.
--
-- Therefore a GLOBAL constructor
--
--   produce : (phi : Cook.BooleanFormula) -> StructuralRepresentativeChain phi
--
-- is already an exact SAT decision procedure:
--
--   decide(phi) := chainTruth(produce phi).
--
-- This owner proves that statement directly.  It prevents the live P9 theorem
-- from silently broadening from one special self-diagonal restriction family
-- to all SAT formulas.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed

------------------------------------------------------------------------
-- Global producer.
------------------------------------------------------------------------

GlobalStructuralChainProducer : Set₁
GlobalStructuralChainProducer =
  (formula : Cook.BooleanFormula) ->
  Closed.StructuralRepresentativeChain formula

------------------------------------------------------------------------
-- Classifier extracted from the chain producer.
------------------------------------------------------------------------

structuralChainDecision :
  GlobalStructuralChainProducer ->
  Cook.BooleanFormula ->
  Bool
structuralChainDecision producer formula =
  Closed.chainTruth
    (producer formula)

------------------------------------------------------------------------
-- Exact SAT soundness/completeness.
------------------------------------------------------------------------

structuralChainDecisionSound :
  (producer : GlobalStructuralChainProducer) ->
  (formula : Cook.BooleanFormula) ->
  structuralChainDecision producer formula ≡ true ->
  Cook.Satisfiable formula
structuralChainDecisionSound producer formula accepted =
  Closed.chainTruthTrueGivesSatisfiable
    (producer formula)
    accepted

structuralChainDecisionComplete :
  (producer : GlobalStructuralChainProducer) ->
  (formula : Cook.BooleanFormula) ->
  Cook.Satisfiable formula ->
  structuralChainDecision producer formula ≡ true
structuralChainDecisionComplete producer formula satisfiable =
  Closed.satisfiableGivesChainTruthTrue
    (producer formula)
    satisfiable

------------------------------------------------------------------------
-- Exact decision package, deliberately independent of any PolynomialCostModel.
------------------------------------------------------------------------

record ExactSATDecision : Set₁ where
  constructor exact-sat-decision
  field
    decide :
      Cook.BooleanFormula ->
      Bool

    sound :
      (formula : Cook.BooleanFormula) ->
      decide formula ≡ true ->
      Cook.Satisfiable formula

    complete :
      (formula : Cook.BooleanFormula) ->
      Cook.Satisfiable formula ->
      decide formula ≡ true

open ExactSATDecision public

globalStructuralChainProducerGivesExactSATDecision :
  GlobalStructuralChainProducer ->
  ExactSATDecision
globalStructuralChainProducerGivesExactSATDecision producer =
  exact-sat-decision
    (structuralChainDecision producer)
    (structuralChainDecisionSound producer)
    (structuralChainDecisionComplete producer)

------------------------------------------------------------------------
-- Research consequence.
--
-- "Construct a structural chain for every SAT formula" is not a useful
-- intermediate theorem: it already constructs exact SAT truth.
--
-- The Clay-facing route must stay narrowly scoped:
--
--   finite code(D) + special self-instantiation root
--      -> chains only for states/restrictions reachable in THAT root-scoped
--         quotient.
--
-- Any proof that broadens the constructor to arbitrary formulas has simply
-- rebuilt a SAT solver.
------------------------------------------------------------------------
