module DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact where

------------------------------------------------------------------------
-- RESOURCE-CLOSING SEMANTIC QUOTIENT SPECIFICATION
--
-- Domain:
--   descendants of ONE fixed indexed root formula under repeated Shannon
--   restrictions.
--
-- This is intentionally narrower than a global SAT quotient.
--
-- A finite quotient supplies:
--
--   State = Fin stateCount
--   classify : reachable restriction derivation -> State
--   step     : State -> Bool -> State
--
-- with exact transition compatibility and semantic congruence on reachable
-- descendants.
--
-- This owner DOES NOT construct the missing quotient.  It types the exact
-- theorem P9 must inhabit and proves useful consequences:
--
--   equal quotient state -> equal decision under every exact SAT oracle.
--
-- It also gives a literal finite transition-table size.  Construction cost of
-- the classifier remains separate and must not be hidden in this graph count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Equisatisfiability for possibly different remaining variable counts.
------------------------------------------------------------------------

SatisfiabilityEquivalent :
  ∀ {leftVariables rightVariables : Nat} →
  SAT.BooleanFormula leftVariables →
  SAT.BooleanFormula rightVariables →
  Set
SatisfiabilityEquivalent left right =
  (SAT.Satisfying left → SAT.Satisfying right)
  ×
  (SAT.Satisfying right → SAT.Satisfying left)

------------------------------------------------------------------------
-- Root-scoped finite quotient automaton.
------------------------------------------------------------------------

record RestrictionSemanticQuotient
    {rootVariables : Nat}
    (root : SAT.BooleanFormula rootVariables) : Set₁ where
  constructor restriction-semantic-quotient
  field
    stateCount : Nat

    classify :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula currentVariables} →
      Family.RestrictionDerivation root current →
      Fin stateCount

    step :
      Fin stateCount →
      Bool →
      Fin stateCount

    falseStepCompatible :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula (suc currentVariables)}
        (derivation :
          Family.RestrictionDerivation root current) →
      classify
        (Family.restrictionFalse derivation)
      ≡
      step
        (classify derivation)
        false

    trueStepCompatible :
      ∀ {currentVariables : Nat}
        {current : SAT.BooleanFormula (suc currentVariables)}
        (derivation :
          Family.RestrictionDerivation root current) →
      classify
        (Family.restrictionTrue derivation)
      ≡
      step
        (classify derivation)
        true

    sameStateImpliesSatisfiabilityEquivalent :
      ∀ {leftVariables rightVariables : Nat}
        {left : SAT.BooleanFormula leftVariables}
        {right : SAT.BooleanFormula rightVariables}
        (leftDerivation :
          Family.RestrictionDerivation root left)
        (rightDerivation :
          Family.RestrictionDerivation root right) →
      classify leftDerivation
      ≡ classify rightDerivation →
      SatisfiabilityEquivalent left right

open RestrictionSemanticQuotient public

------------------------------------------------------------------------
-- Semantic consequence: quotient state determines every exact SAT-oracle bit
-- on reachable nodes.
------------------------------------------------------------------------

sameStateImpliesSameOracleDecision :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : RestrictionSemanticQuotient root)
    (oracle : SAT.SATDecisionOracle)
    {leftVariables rightVariables : Nat}
    {left : SAT.BooleanFormula leftVariables}
    {right : SAT.BooleanFormula rightVariables}
    (leftDerivation :
      Family.RestrictionDerivation root left)
    (rightDerivation :
      Family.RestrictionDerivation root right) →
  classify quotient leftDerivation
  ≡ classify quotient rightDerivation →
  Search.decide oracle left
  ≡ Search.decide oracle right
sameStateImpliesSameOracleDecision
    quotient
    oracle
    {left = left}
    {right = right}
    leftDerivation
    rightDerivation
    sameState
    with Search.decide oracle left
       | Search.decide oracle right
... | true | true =
  refl
... | false | false =
  refl
... | true | false =
  falseNotTrue
    (Search.complete
      oracle
      right
      (proj₁ equivalent
        (Search.sound oracle left refl)))
  where
    equivalent :
      SatisfiabilityEquivalent left right
    equivalent =
      sameStateImpliesSatisfiabilityEquivalent
        quotient
        leftDerivation
        rightDerivation
        sameState
... | false | true =
  falseNotTrue
    (Search.complete
      oracle
      left
      (proj₂ equivalent
        (Search.sound oracle right refl)))
  where
    equivalent :
      SatisfiabilityEquivalent left right
    equivalent =
      sameStateImpliesSatisfiabilityEquivalent
        quotient
        leftDerivation
        rightDerivation
        sameState

------------------------------------------------------------------------
-- Quotient transitions preserve exact Shannon-child classification.
------------------------------------------------------------------------

falseChildState :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula (suc currentVariables)}
    (derivation :
      Family.RestrictionDerivation root current) →
  classify quotient
    (Family.restrictionFalse derivation)
  ≡
  step quotient
    (classify quotient derivation)
    false
falseChildState =
  falseStepCompatible

trueChildState :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : RestrictionSemanticQuotient root)
    {current : SAT.BooleanFormula (suc currentVariables)}
    (derivation :
      Family.RestrictionDerivation root current) →
  classify quotient
    (Family.restrictionTrue derivation)
  ≡
  step quotient
    (classify quotient derivation)
    true
trueChildState =
  trueStepCompatible

------------------------------------------------------------------------
-- Literal finite graph accounting.
--
-- Each state stores one node plus two outgoing Boolean-labelled transitions.
------------------------------------------------------------------------

quotientTransitionCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  RestrictionSemanticQuotient root →
  Nat
quotientTransitionCount quotient =
  (suc (suc zero))
  * stateCount quotient

quotientGraphCellCount :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables} →
  RestrictionSemanticQuotient root →
  Nat
quotientGraphCellCount quotient =
  stateCount quotient
  +
  quotientTransitionCount quotient

record QuotientGraphFitsBudget
    {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (quotient : RestrictionSemanticQuotient root)
    (budget : Nat) : Set where
  constructor quotient-graph-fits-budget
  field
    graphFits :
      quotientGraphCellCount quotient
      ≤ budget

open QuotientGraphFitsBudget public

------------------------------------------------------------------------
-- IMPORTANT RESOURCE BOUNDARY
--
-- QuotientGraphFitsBudget counts only the represented finite state graph.
-- It does NOT prove that classify is cheap or non-circular.
--
-- A Clay-relevant P9 inhabitant must additionally construct classify from the
-- finite program/self-instantiation structure without calling the target SAT
-- decision on the restricted node.  That construction theorem is still open.
------------------------------------------------------------------------
