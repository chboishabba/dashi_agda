module DASHI.Mathematics.Complexity.PNotEqualsNPSATTruthQuotientCircularityExact where

------------------------------------------------------------------------
-- TRUTH-ONLY SEMANTIC QUOTIENT: TWO CLASSES ARE TRIVIAL BUT CIRCULAR
--
-- Correction to the stronger BDD/subfunction quotient route:
--
-- P9's MINIMAL semantic obligation is only
--
--   Q(phi) = Q(psi)
--      =>
--   SAT(phi) <-> SAT(psi),
--
-- not equality of the full residual Boolean functions.
--
-- At that truth-only level there is never an information-theoretic class-count
-- obstacle: every exact SAT oracle itself induces a Boolean two-class quotient
--
--   Q_D(phi) := D(phi).
--
-- Equal class bits imply equisatisfiability by soundness/completeness.
--
-- But computing Q_D is literally making the SAT decision we were trying to
-- replace.  So obligations "few classes" + "truth soundness" are insufficient;
-- cheap NON-CIRCULAR construction is the decisive requirement.
--
-- This owner makes that distinction theorem-level rather than editorial.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.SATDecisionToWitnessSelfReductionExact as Search
import DASHI.Mathematics.Complexity.BooleanFormulaFiniteSATDecisionExact as Finite

------------------------------------------------------------------------
-- Equisatisfiability.
------------------------------------------------------------------------

SatisfiabilityEquivalent :
  ∀ {variables}
    (left right : SAT.BooleanFormula variables) →
  Set
SatisfiabilityEquivalent left right =
  (SAT.Satisfying left → SAT.Satisfying right)
  ×
  (SAT.Satisfying right → SAT.Satisfying left)

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Every exact SAT oracle is itself a two-class truth quotient.
------------------------------------------------------------------------

oracleTruthClass :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables} →
  SAT.BooleanFormula variables →
  Bool
oracleTruthClass oracle =
  Search.decide oracle

sameOracleTruthClassImpliesSatisfiabilityEquivalent :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables}
    (left right : SAT.BooleanFormula variables) →
  oracleTruthClass oracle left
  ≡ oracleTruthClass oracle right →
  SatisfiabilityEquivalent left right
sameOracleTruthClassImpliesSatisfiabilityEquivalent
    oracle left right same
    with oracleTruthClass oracle left
       | oracleTruthClass oracle right
       | same
... | true | true | refl =
  (λ leftSat →
    Search.sound oracle right refl)
  ,
  (λ rightSat →
    Search.sound oracle left refl)
... | false | false | refl =
  impossibleLeft
  ,
  impossibleRight
  where
    impossibleLeft :
      SAT.Satisfying left →
      SAT.Satisfying right
    impossibleLeft leftSat =
      ⊥-elim
        (falseNotTrue
          (Search.complete
            oracle
            left
            leftSat))

    impossibleRight :
      SAT.Satisfying right →
      SAT.Satisfying left
    impossibleRight rightSat =
      ⊥-elim
        (falseNotTrue
          (Search.complete
            oracle
            right
            rightSat))

------------------------------------------------------------------------
-- The quotient classifier is definitionally the decision procedure.
------------------------------------------------------------------------

truthClassIsOracleDecision :
  (oracle : SAT.SATDecisionOracle) →
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  oracleTruthClass oracle formula
  ≡ Search.decide oracle formula
truthClassIsOracleDecision oracle formula =
  refl

------------------------------------------------------------------------
-- Constructive exact SAT decider specialization.
--
-- The repository's finite SAT decider therefore also gives a two-class
-- semantic quotient without any hypothetical P-time assumption.
------------------------------------------------------------------------

finiteTruthClass :
  ∀ {variables} →
  SAT.BooleanFormula variables →
  Bool
finiteTruthClass =
  Finite.decideFiniteSATBool

finiteTruthClassSound :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  finiteTruthClass formula ≡ true →
  SAT.Satisfying formula
finiteTruthClassSound =
  Finite.decideFiniteSATBoolSound

finiteTruthClassComplete :
  ∀ {variables}
    (formula : SAT.BooleanFormula variables) →
  SAT.Satisfying formula →
  finiteTruthClass formula ≡ true
finiteTruthClassComplete =
  Finite.decideFiniteSATBoolComplete

------------------------------------------------------------------------
-- Research consequence.
--
-- Truth-only quotient image size is NEVER the hard part: two classes suffice.
--
-- The hard P9 theorem must therefore constrain the CLASSIFIER CONSTRUCTION:
--
--   code(D), partial self-assignment
--       -> Q_D(a)
--
-- without simply calling D(phi_a), calling another SAT decider, or otherwise
-- evaluating the target truth first.
--
-- The stronger equality/BDD owners remain useful for the distinct proposal
-- where Q preserves complete residual-subfunction semantics.  They must not be
-- advertised as a lower bound on the minimal truth-only P9 quotient.
------------------------------------------------------------------------
