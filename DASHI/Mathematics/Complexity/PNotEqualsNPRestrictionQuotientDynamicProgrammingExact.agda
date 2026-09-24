module DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientDynamicProgrammingExact where

------------------------------------------------------------------------
-- FINITE RESTRICTION QUOTIENT -> POLYNOMIAL-SIZED SHANNON DYNAMIC PROGRAM
--
-- Given a root-scoped finite restriction quotient:
--
--   classify : reachable node -> Fin stateCount
--   step     : state -> Bool -> state
--
-- and a correct truth label for reachable terminal (zero-variable) states,
-- define:
--
--   V_0(q)     = terminalTruth(q)
--   V_(d+1)(q) = V_d(step(q,false)) OR V_d(step(q,true)).
--
-- Main theorem:
--
--   for EVERY reachable d-variable restricted formula phi,
--
--     V_d(classify(phi)) = exactSATDecision(phi).
--
-- Thus the full 2^n Shannon tree is replaced by a depth-by-state table with
--
--   (n + 1) * stateCount
--
-- Boolean cells.
--
-- This is the precise resource payoff P9 is searching for.
--
-- IMPORTANT:
-- The theorem is conditional on CONSTRUCTING the quotient and terminal labels.
-- It does not provide the missing non-circular classifier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPSATShannonSemanticAuthorityExact as Shannon

------------------------------------------------------------------------
-- Terminal truth labels.
------------------------------------------------------------------------

record TerminalStateLabelling
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle) : Set₁ where
  constructor terminal-state-labelling
  field
    terminalTruth :
      Fin (Quotient.stateCount quotient) →
      Bool

    terminalTruthCorrect :
      ∀ {terminal : SAT.BooleanFormula zero}
        (derivation :
          Family.RestrictionDerivation root terminal) →
      terminalTruth
        (Quotient.classify quotient derivation)
      ≡
      Search.decide oracle terminal

open TerminalStateLabelling public

------------------------------------------------------------------------
-- Dynamic-program value at remaining variable depth.
------------------------------------------------------------------------

quotientTruthAtDepth :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    {oracle : SAT.SATDecisionOracle} →
  TerminalStateLabelling quotient oracle →
  Nat →
  Fin (Quotient.stateCount quotient) →
  Bool
quotientTruthAtDepth quotient labels zero state =
  terminalTruth labels state
quotientTruthAtDepth quotient labels (suc depth) state =
  SAT.orBool
    (quotientTruthAtDepth
      quotient
      labels
      depth
      (Quotient.step quotient state false))
    (quotientTruthAtDepth
      quotient
      labels
      depth
      (Quotient.step quotient state true))

------------------------------------------------------------------------
-- Main correctness theorem.
------------------------------------------------------------------------

quotientTruthComputesReachableDecision :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : TerminalStateLabelling quotient oracle)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables}
    (derivation :
      Family.RestrictionDerivation root current) →
  quotientTruthAtDepth
    quotient
    labels
    currentVariables
    (Quotient.classify quotient derivation)
  ≡
  Search.decide oracle current
quotientTruthComputesReachableDecision
    quotient
    oracle
    labels
    {currentVariables = zero}
    derivation =
  terminalTruthCorrect
    labels
    derivation
quotientTruthComputesReachableDecision
    {root = root}
    quotient
    oracle
    labels
    {currentVariables = suc depth}
    {current = current}
    derivation =
  trans
    childValuesBecomeDecisions
    (sym
      (Shannon.satDecisionShannon
        oracle
        current))
  where
    falseDerivation :
      Family.RestrictionDerivation
        root
        (SAT.restrictHead false current)
    falseDerivation =
      Family.restrictionFalse derivation

    trueDerivation :
      Family.RestrictionDerivation
        root
        (SAT.restrictHead true current)
    trueDerivation =
      Family.restrictionTrue derivation

    falseStateCompatibility :
      Quotient.step quotient
        (Quotient.classify quotient derivation)
        false
      ≡
      Quotient.classify quotient falseDerivation
    falseStateCompatibility =
      sym
        (Quotient.falseStepCompatible
          quotient
          derivation)

    trueStateCompatibility :
      Quotient.step quotient
        (Quotient.classify quotient derivation)
        true
      ≡
      Quotient.classify quotient trueDerivation
    trueStateCompatibility =
      sym
        (Quotient.trueStepCompatible
          quotient
          derivation)

    falseValue :
      quotientTruthAtDepth
        quotient
        labels
        depth
        (Quotient.step quotient
          (Quotient.classify quotient derivation)
          false)
      ≡
      Search.decide oracle
        (SAT.restrictHead false current)
    falseValue =
      trans
        (congruenceState
          falseStateCompatibility)
        (quotientTruthComputesReachableDecision
          quotient
          oracle
          labels
          falseDerivation)
      where
        congruenceState :
          ∀ {left right :
              Fin (Quotient.stateCount quotient)} →
          left ≡ right →
          quotientTruthAtDepth
            quotient labels depth left
          ≡
          quotientTruthAtDepth
            quotient labels depth right
        congruenceState refl =
          refl

    trueValue :
      quotientTruthAtDepth
        quotient
        labels
        depth
        (Quotient.step quotient
          (Quotient.classify quotient derivation)
          true)
      ≡
      Search.decide oracle
        (SAT.restrictHead true current)
    trueValue =
      trans
        (congruenceState
          trueStateCompatibility)
        (quotientTruthComputesReachableDecision
          quotient
          oracle
          labels
          trueDerivation)
      where
        congruenceState :
          ∀ {left right :
              Fin (Quotient.stateCount quotient)} →
          left ≡ right →
          quotientTruthAtDepth
            quotient labels depth left
          ≡
          quotientTruthAtDepth
            quotient labels depth right
        congruenceState refl =
          refl

    childValuesBecomeDecisions :
      SAT.orBool
        (quotientTruthAtDepth
          quotient
          labels
          depth
          (Quotient.step quotient
            (Quotient.classify quotient derivation)
            false))
        (quotientTruthAtDepth
          quotient
          labels
          depth
          (Quotient.step quotient
            (Quotient.classify quotient derivation)
            true))
      ≡
      SAT.orBool
        (Search.decide oracle
          (SAT.restrictHead false current))
        (Search.decide oracle
          (SAT.restrictHead true current))
    childValuesBecomeDecisions =
      cong₂
        SAT.orBool
        falseValue
        trueValue

------------------------------------------------------------------------
-- Root specialization.
------------------------------------------------------------------------

quotientTruthComputesRootDecision :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : Quotient.RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    (labels : TerminalStateLabelling quotient oracle) →
  quotientTruthAtDepth
    quotient
    labels
    rootVariables
    (Quotient.classify quotient Family.restrictionRoot)
  ≡
  Search.decide oracle root
quotientTruthComputesRootDecision
    quotient oracle labels =
  quotientTruthComputesReachableDecision
    quotient
    oracle
    labels
    Family.restrictionRoot

------------------------------------------------------------------------
-- Exact finite table size.
------------------------------------------------------------------------

quotientDynamicTableCellCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  Quotient.RestrictionSemanticQuotient root →
  Nat
quotientDynamicTableCellCount
    {rootVariables}
    quotient =
  suc rootVariables
  * Quotient.stateCount quotient

------------------------------------------------------------------------
-- Resource interpretation.
--
-- A producer with polynomially/sufficiently small stateCount can represent the
-- exact Shannon evaluation using only depth-by-state cells rather than 2^n
-- restriction leaves.
--
-- The remaining hard theorem is therefore exactly what the user identified:
-- construct the state quotient and its terminal labelling NON-CIRCULARLY from
-- the described self-instantiation machinery, with this table plus quotient
-- graph fitting the self-size budget.
------------------------------------------------------------------------
