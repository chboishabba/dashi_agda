module DASHI.Mathematics.Complexity.PNotEqualsNPResourceBoundedSelfDiagonalExact where

------------------------------------------------------------------------
-- RESOURCE-BOUNDED SELF-DIAGONAL SAT
--
-- Repo-native DASHI extension, calibrated by:
--
--   * Cook 1971 for polynomial computation -> propositional encoding ancestry;
--   * Kleene 1952 for computability-level self-reference ancestry;
--   * Baker--Gill--Solovay / Razborov--Rudich / Aaronson--Wigderson for
--     lower-bound barrier discipline.
--
-- Exact bibliographic metadata and source boundaries live in:
--
--   PNotEqualsNPDiagonalizationSourceAtlasExact.
--
-- NO external source is attributed the theorem attempted here.
--
-- This owner separates two questions that ordinary diagonalization conflates:
--
--   SEMANTICS:
--     construct phi_D with
--       SAT(phi_D) <-> D(phi_D) = false.
--
--   RESOURCE CLOSURE:
--     represent the self-evaluation of D on phi_D inside a formula whose own
--     size is compatible with that evaluation cost.
--
-- A semantic witness immediately forces D to be wrong.  Separately, a literal
-- explicit tableau cannot be the resource-closure mechanism at any self-size
-- where D's runtime strictly exceeds the available formula size and the
-- encoding needs at least one formula unit per simulated step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPDiagonalizationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- Tiny logical utilities.
------------------------------------------------------------------------

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- The semantic fixed-point target.
--
-- This is already decisive mathematics: no claim is made that classical
-- recursion theorems construct this same-object propositional witness within
-- the required resource budget.
------------------------------------------------------------------------

record SelfDiagonalSemanticWitness
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  constructor self-diagonal-semantic-witness
  field
    formula : Cook.BooleanFormula

    satisfiableIfRejects :
      Direct.decide candidate formula ≡ false →
      Cook.Satisfiable formula

    rejectsIfSatisfiable :
      Cook.Satisfiable formula →
      Direct.decide candidate formula ≡ false

open SelfDiagonalSemanticWitness public

selfDiagonalSemanticWitnessGivesFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  SelfDiagonalSemanticWitness candidate →
  Direct.SATDecisionFailure candidate
selfDiagonalSemanticWitnessGivesFailure {candidate = candidate} witness
    with Direct.decide candidate (formula witness)
... | false =
  Direct.falseNegative
    (formula witness)
    (satisfiableIfRejects witness refl)
    refl
... | true =
  Direct.falsePositive
    (formula witness)
    refl
    unsatisfiable
  where
    unsatisfiable :
      Cook.Satisfiable (formula witness) → ⊥
    unsatisfiable satisfiable =
      trueNotFalse
        (rejectsIfSatisfiable witness satisfiable)

------------------------------------------------------------------------
-- Universal self-diagonal semantics would immediately close the Clay core.
------------------------------------------------------------------------

UniversalPolynomialSATSelfDiagonal :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
UniversalPolynomialSATSelfDiagonal cost =
  (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  SelfDiagonalSemanticWitness candidate

universalSelfDiagonalGivesUniversalDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATSelfDiagonal cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
universalSelfDiagonalGivesUniversalDecisionFailure selfDiagonal candidate =
  selfDiagonalSemanticWitnessGivesFailure
    (selfDiagonal candidate)

universalSelfDiagonalGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalPolynomialSATSelfDiagonal cost →
  Clay.SATLowerBoundProducer cost
universalSelfDiagonalGivesSATLowerBoundProducer selfDiagonal =
  Direct.universalDecisionFailureGivesSATLowerBoundProducer
    (universalSelfDiagonalGivesUniversalDecisionFailure selfDiagonal)

------------------------------------------------------------------------
-- SIZE ACCOUNTING FOR A LITERAL EXPLICIT SELF-TABLEAU
--
-- This record is intentionally weaker than a full self-diagonal construction.
-- It records only the resource equations needed to expose the standard-tableau
-- obstruction at one proposed self-generated formula.
------------------------------------------------------------------------

record ExplicitSelfTableauSizeAttempt
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  constructor explicit-self-tableau-size-attempt
  field
    formula : Cook.BooleanFormula

    formulaSize : Nat
    selfEvaluationSteps : Nat

    -- A literal tableau/certificate which explicitly represents every
    -- simulated step needs room for at least the self-evaluation length.
    explicitTableauNeedsEachStep :
      selfEvaluationSteps ≤ formulaSize

    -- The problematic regime: on this very self-generated formula the
    -- candidate's evaluation takes strictly more steps than the formula has
    -- available size units.
    selfRuntimeStrictlyExceedsFormula :
      formulaSize < selfEvaluationSteps

open ExplicitSelfTableauSizeAttempt public

explicitSelfTableauCannotClose :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  ExplicitSelfTableauSizeAttempt candidate →
  ⊥
explicitSelfTableauCannotClose attempt =
  NatP.<-irrefl
    (formulaSize attempt)
    (NatP.<-≤-trans
      (selfRuntimeStrictlyExceedsFormula attempt)
      (explicitTableauNeedsEachStep attempt))

------------------------------------------------------------------------
-- Abstract runtime/encoding functions expose the fixed-point-compatible seam.
------------------------------------------------------------------------

record SelfEvaluationCostModel
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  field
    formulaSize :
      Cook.BooleanFormula → Nat

    selfEvaluationSteps :
      Cook.BooleanFormula → Nat

open SelfEvaluationCostModel public

record ExplicitTableauEncodingRule
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (resource : SelfEvaluationCostModel candidate) : Set₁ where
  field
    explicitTableauLowerBound :
      (formula : Cook.BooleanFormula) →
      SelfEvaluationCostModel.selfEvaluationSteps resource formula
      ≤
      SelfEvaluationCostModel.formulaSize resource formula

open ExplicitTableauEncodingRule public

record SuperlinearAtSelfFormula
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (resource : SelfEvaluationCostModel candidate)
    (formula : Cook.BooleanFormula) : Set where
  constructor superlinear-at-self-formula
  field
    strict :
      SelfEvaluationCostModel.formulaSize resource formula
      <
      SelfEvaluationCostModel.selfEvaluationSteps resource formula

open SuperlinearAtSelfFormula public

explicitTableauRuleCannotEncodeSuperlinearSelfFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate} →
  ExplicitTableauEncodingRule resource →
  (formula : Cook.BooleanFormula) →
  SuperlinearAtSelfFormula resource formula →
  ⊥
explicitTableauRuleCannotEncodeSuperlinearSelfFormula
    rule formula superlinear =
  NatP.<-irrefl
    (SelfEvaluationCostModel.formulaSize resource formula)
    (NatP.<-≤-trans
      (strict superlinear)
      (explicitTableauLowerBound rule formula))

------------------------------------------------------------------------
-- What a successful succinct mechanism has to beat.
--
-- "Succinct" here is only size accounting.  It is deliberately separated from
-- semantic correctness so that a small DAG/recursive certificate is not
-- silently promoted into a self-diagonal theorem.
------------------------------------------------------------------------

record FixedPointCompatibleCertificateSize
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (resource : SelfEvaluationCostModel candidate)
    (formula : Cook.BooleanFormula) : Set where
  constructor fixed-point-compatible-certificate-size
  field
    certificateSize : Nat

    certificateFitsInsideFormula :
      certificateSize
      ≤ SelfEvaluationCostModel.formulaSize resource formula

    certificateStrictlySmallerThanSelfEvaluation :
      certificateSize
      < SelfEvaluationCostModel.selfEvaluationSteps resource formula

open FixedPointCompatibleCertificateSize public

record SelfDiagonalSuccinctCertificate
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (resource : SelfEvaluationCostModel candidate) : Set₁ where
  constructor self-diagonal-succinct-certificate
  field
    semanticWitness :
      SelfDiagonalSemanticWitness candidate

    sizeWitness :
      FixedPointCompatibleCertificateSize
        resource
        (SelfDiagonalSemanticWitness.formula semanticWitness)

open SelfDiagonalSuccinctCertificate public

succinctSelfDiagonalCertificateGivesFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate} →
  SelfDiagonalSuccinctCertificate resource →
  Direct.SATDecisionFailure candidate
succinctSelfDiagonalCertificateGivesFailure certificate =
  selfDiagonalSemanticWitnessGivesFailure
    (semanticWitness certificate)


------------------------------------------------------------------------
-- Universal succinct self-diagonal producer.
--
-- This is deliberately stronger than bare SATNotInP: it constructs, for every
-- polynomial SAT candidate, a same-object self-diagonal formula together with
-- a certificate which fits inside that formula and is strictly smaller than
-- the candidate's full self-evaluation trajectory.
------------------------------------------------------------------------

UniversalSelfDiagonalSuccinctCertificate :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  ((candidate : Direct.PolynomialSATDeciderCandidate cost) →
    SelfEvaluationCostModel candidate) →
  Set₁
UniversalSelfDiagonalSuccinctCertificate cost resourceFor =
  (candidate : Direct.PolynomialSATDeciderCandidate cost) →
  SelfDiagonalSuccinctCertificate (resourceFor candidate)

universalSuccinctSelfDiagonalGivesUniversalDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {resourceFor :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      SelfEvaluationCostModel candidate} →
  UniversalSelfDiagonalSuccinctCertificate cost resourceFor →
  Direct.UniversalPolynomialSATDecisionFailure cost
universalSuccinctSelfDiagonalGivesUniversalDecisionFailure
    universalCertificate candidate =
  succinctSelfDiagonalCertificateGivesFailure
    (universalCertificate candidate)

universalSuccinctSelfDiagonalGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {resourceFor :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      SelfEvaluationCostModel candidate} →
  UniversalSelfDiagonalSuccinctCertificate cost resourceFor →
  Clay.SATLowerBoundProducer cost
universalSuccinctSelfDiagonalGivesSATLowerBoundProducer universalCertificate =
  Direct.universalDecisionFailureGivesSATLowerBoundProducer
    (universalSuccinctSelfDiagonalGivesUniversalDecisionFailure
      universalCertificate)
