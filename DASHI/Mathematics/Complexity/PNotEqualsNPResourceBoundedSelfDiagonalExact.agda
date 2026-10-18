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
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPDiagonalizationSourceAtlasExact as Sources
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

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
-- Quadratic specialization of the size obstruction.
--
-- Once the self-generated formula has size N >= 2, N < N^2.  Hence any
-- candidate whose self-evaluation takes at least N^2 steps cannot be encoded by
-- a literal one-formula-unit-per-step tableau inside that same N-size formula.
------------------------------------------------------------------------

two : Nat
two = suc (suc zero)

sizeAtLeastTwoImpliesBelowSquare :
  ∀ {size : Nat} →
  two ≤ size →
  size < size * size
sizeAtLeastTwoImpliesBelowSquare {zero} ()
sizeAtLeastTwoImpliesBelowSquare
    {suc zero} ()
sizeAtLeastTwoImpliesBelowSquare
    {size@(suc
      (suc rest))}
    two≤size =
  subst
    (λ left → left < size * size)
    (NatP.*-identityˡ size)
    (NatP.*-monoˡ-< size two≤size)

record QuadraticExplicitSelfTableauAttempt
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  constructor quadratic-explicit-self-tableau-attempt
  field
    formula : Cook.BooleanFormula
    formulaSize : Nat
    selfEvaluationSteps : Nat

    formulaHasNontrivialSize :
      two ≤ formulaSize

    quadraticSelfRuntimeLowerBound :
      formulaSize * formulaSize
      ≤ selfEvaluationSteps

    explicitTableauNeedsEachStep :
      selfEvaluationSteps ≤ formulaSize

open QuadraticExplicitSelfTableauAttempt public

quadraticExplicitSelfTableauCannotClose :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  QuadraticExplicitSelfTableauAttempt candidate →
  ⊥
quadraticExplicitSelfTableauCannotClose attempt =
  NatP.<-irrefl
    (QuadraticExplicitSelfTableauAttempt.formulaSize attempt)
    (NatP.<-≤-trans
      (NatP.<-≤-trans
        (sizeAtLeastTwoImpliesBelowSquare
          (formulaHasNontrivialSize attempt))
        (quadraticSelfRuntimeLowerBound attempt))
      (QuadraticExplicitSelfTableauAttempt.explicitTableauNeedsEachStep
        attempt))

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
-- QUADRATIC SELF-RUNTIME SPECIALIZATION
--
-- The abstract no-go above takes a strict self-runtime inequality as input.
-- The first genuinely superlinear polynomial case can be paid arithmetically:
--
--   N >= 2  and  N^2 <= T_D(phi)
--          =>
--   N < T_D(phi).
--
-- Thus any literal one-formula-unit-per-step tableau is impossible at such a
-- self-generated formula.  This is the concrete N versus N^2 obstruction
-- discussed in the diagonal programme; it is repo-native arithmetic, not an
-- imported complexity theorem.
------------------------------------------------------------------------


zeroLessThanTwo : zero < two
zeroLessThanTwo =
  s≤s z≤n

leftStrictAddPositive :
  (left right : Nat) →
  zero < right →
  left < left + right
leftStrictAddPositive zero right rightPositive =
  rightPositive
leftStrictAddPositive (suc left) right rightPositive =
  s≤s
    (leftStrictAddPositive left right rightPositive)

squareStrictlyAboveAtLeastTwo :
  (n : Nat) →
  two ≤ n →
  n < n * n
squareStrictlyAboveAtLeastTwo n twoLeN =
  NatP.<-≤-trans
    nBelowDouble
    (NatP.*-monoʳ-≤ n twoLeN)
  where
    nPositive : zero < n
    nPositive =
      NatP.<-≤-trans
        zeroLessThanTwo
        twoLeN

    nBelowDouble : n < n * two
    nBelowDouble =
      leftStrictAddPositive n n nPositive

quadraticRuntimeStrictlyExceedsFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate}
    (formula : Cook.BooleanFormula) →
  two ≤ SelfEvaluationCostModel.formulaSize resource formula →
  SelfEvaluationCostModel.formulaSize resource formula
    * SelfEvaluationCostModel.formulaSize resource formula
    ≤ SelfEvaluationCostModel.selfEvaluationSteps resource formula →
  SuperlinearAtSelfFormula resource formula
quadraticRuntimeStrictlyExceedsFormula
    {resource = resource}
    formula sizeAtLeastTwo quadraticLowerBound =
  superlinear-at-self-formula
    (NatP.<-≤-trans
      (squareStrictlyAboveAtLeastTwo
        (SelfEvaluationCostModel.formulaSize resource formula)
        sizeAtLeastTwo)
      quadraticLowerBound)

explicitTableauRuleCannotEncodeQuadraticSelfFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate} →
  ExplicitTableauEncodingRule resource →
  (formula : Cook.BooleanFormula) →
  two ≤ SelfEvaluationCostModel.formulaSize resource formula →
  SelfEvaluationCostModel.formulaSize resource formula
    * SelfEvaluationCostModel.formulaSize resource formula
    ≤ SelfEvaluationCostModel.selfEvaluationSteps resource formula →
  ⊥
explicitTableauRuleCannotEncodeQuadraticSelfFormula
    {resource = resource}
    rule formula sizeAtLeastTwo quadraticLowerBound =
  explicitTableauRuleCannotEncodeSuperlinearSelfFormula
    rule
    formula
    (quadraticRuntimeStrictlyExceedsFormula
      formula
      sizeAtLeastTwo
      quadraticLowerBound)


------------------------------------------------------------------------
-- ARBITRARY DEGREE >= 2 MONOMIAL SPECIALIZATION
--
-- For n >= 2, every monomial n^(2+r) dominates n^2 and therefore strictly
-- exceeds n.  This turns any self-runtime lower bound of degree at least two
-- into the same explicit-tableau contradiction.
------------------------------------------------------------------------

powAtLeastSquare :
  (n extraDegree : Nat) →
  suc zero ≤ n →
  n * n ≤ ERQ.pow n (suc (suc extraDegree))
powAtLeastSquare n zero nPositive =
  NatP.≤-refl
powAtLeastSquare n (suc extraDegree) nPositive =
  NatP.≤-trans
    (powAtLeastSquare n extraDegree nPositive)
    previousPowerBelowNext
  where
    previousPower :
      Nat
    previousPower =
      ERQ.pow n (suc (suc extraDegree))

    previousPowerBelowNext :
      previousPower
      ≤ ERQ.pow n (suc (suc (suc extraDegree)))
    previousPowerBelowNext =
      NatP.≤-trans
        (NatP.m≤m*n previousPower n)
        (NatP.≤-reflexive
          (NatP.*-comm previousPower n))

monomialRuntimeStrictlyExceedsFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate}
    (formula : Cook.BooleanFormula)
    (extraDegree : Nat) →
  two ≤ SelfEvaluationCostModel.formulaSize resource formula →
  ERQ.pow
      (SelfEvaluationCostModel.formulaSize resource formula)
      (suc (suc extraDegree))
    ≤ SelfEvaluationCostModel.selfEvaluationSteps resource formula →
  SuperlinearAtSelfFormula resource formula
monomialRuntimeStrictlyExceedsFormula
    {resource = resource}
    formula extraDegree sizeAtLeastTwo monomialLowerBound =
  superlinear-at-self-formula
    (NatP.<-≤-trans
      (squareStrictlyAboveAtLeastTwo size sizeAtLeastTwo)
      (NatP.≤-trans
        (powAtLeastSquare
          size
          extraDegree
          sizePositive)
        monomialLowerBound))
  where
    size :
      Nat
    size =
      SelfEvaluationCostModel.formulaSize resource formula

    sizePositive :
      suc zero ≤ size
    sizePositive =
      NatP.≤-trans
        (s≤s z≤n)
        sizeAtLeastTwo

explicitTableauRuleCannotEncodeDegreeAtLeastTwoSelfFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {resource : SelfEvaluationCostModel candidate} →
  ExplicitTableauEncodingRule resource →
  (formula : Cook.BooleanFormula)
  (extraDegree : Nat) →
  two ≤ SelfEvaluationCostModel.formulaSize resource formula →
  ERQ.pow
      (SelfEvaluationCostModel.formulaSize resource formula)
      (suc (suc extraDegree))
    ≤ SelfEvaluationCostModel.selfEvaluationSteps resource formula →
  ⊥
explicitTableauRuleCannotEncodeDegreeAtLeastTwoSelfFormula
    rule formula extraDegree sizeAtLeastTwo monomialLowerBound =
  explicitTableauRuleCannotEncodeSuperlinearSelfFormula
    rule
    formula
    (monomialRuntimeStrictlyExceedsFormula
      formula
      extraDegree
      sizeAtLeastTwo
      monomialLowerBound)

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
