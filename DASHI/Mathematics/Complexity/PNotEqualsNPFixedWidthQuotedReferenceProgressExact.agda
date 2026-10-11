module DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthQuotedReferenceProgressExact where

------------------------------------------------------------------------
-- FIXED-WIDTH QUOTED ROOT: THE EXPLICIT REFERENCE CONSTRUCTOR PROGRESSES
--
-- FixedWidthQuotedRootSemanticInertnessExact proves that the current structural
-- self-code quotation has Cook variable bound zero.
--
-- Therefore the all-functions reference automaton contains only the two
-- zero-arity truth functions.  Its exact represented evaluation cost is:
--
--   graph cells = 3 * 2 = 6
--   DP cells    = 1 * 2 = 2
--   constructor functional step = 1
--   next authority formula       = 1 node
--
-- so the nonpersistent charge is 10.
--
-- Independently, the fixed-point structural quotation has at least 17 syntax
-- nodes.  Persistent program-code/rebinding payload occurs on BOTH sides of
-- the recurrence inequality, hence the reference first step strictly fits.
--
-- This pays B/progress for the PRESENT structural quotation.  It does not help
-- the Clay contradiction because that quotation is already proved tautological.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact as SelfQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthQuotedRootSemanticInertnessExact as Inert
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedCompilerExact as Positive
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPArityTerminalDirectDPAuthorityExact as Authority
import DASHI.Mathematics.Complexity.PNotEqualsNPStagedReferenceDirectDPConstructorExact as Reference
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Generic node-count monotonicity for conjunction.
------------------------------------------------------------------------

conjunctionNodeCountLower :
  ∀ {left right : Cook.BooleanFormula}
    {leftLower rightLower : Nat} →
  leftLower ≤ Size.formulaNodeCount left →
  rightLower ≤ Size.formulaNodeCount right →
  suc (leftLower + rightLower)
  ≤
  Size.formulaNodeCount
    (Cook.conjunction left right)
conjunctionNodeCountLower leftProof rightProof =
  s≤s
    (NatP.+-mono-≤ leftProof rightProof)

------------------------------------------------------------------------
-- The structural fixed-point quotation has at least 17 syntax nodes.
------------------------------------------------------------------------

fixedWidthQuotedRootAtLeastSeventeen :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  17
  ≤
  Size.formulaNodeCount
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
fixedWidthQuotedRootAtLeastSeventeen code codec =
  rootLower
  where
    quotation =
      Fixed.fixedWidthCandidateCodeQuotation code codec

    codeFormula : Cook.BooleanFormula
    codeFormula =
      SelfQuote.quoteCandidateCode quotation
        (Actual.CandidateCodeRealization.candidateCode code)

    primitiveFormula : Cook.BooleanFormula
    primitiveFormula =
      SelfQuote.structuralProgramQuote
        quotation
        (Code.primitive SelfQuote.runCandidateOnQuote)

    diagonalFormula : Cook.BooleanFormula
    diagonalFormula =
      SelfQuote.structuralProgramQuote
        quotation
        (Code.diagonalized
          (Code.primitive SelfQuote.runCandidateOnQuote))

    pairFormula : Cook.BooleanFormula
    pairFormula =
      Cook.conjunction diagonalFormula diagonalFormula

    codeLower :
      1 ≤ Size.formulaNodeCount codeFormula
    codeLower =
      Positive.formulaNodeCountPositive codeFormula

    primitiveLower :
      3 ≤ Size.formulaNodeCount primitiveFormula
    primitiveLower =
      conjunctionNodeCountLower
        codeLower
        NatP.≤-refl

    diagonalLower :
      6 ≤ Size.formulaNodeCount diagonalFormula
    diagonalLower =
      conjunctionNodeCountLower
        NatP.≤-refl
        primitiveLower

    pairLower :
      13 ≤ Size.formulaNodeCount pairFormula
    pairLower =
      conjunctionNodeCountLower
        diagonalLower
        diagonalLower

    rootLower :
      17
      ≤
      Size.formulaNodeCount
        (Q2.currentFormula
          (Fixed.fixedWidthCandidateQuotedState code codec))
    rootLower =
      conjunctionNodeCountLower
        NatP.≤-refl
        pairLower

------------------------------------------------------------------------
-- 10 is strictly below the structural root.
------------------------------------------------------------------------

tenLessSeventeen : 10 < 17
tenLessSeventeen =
  NatP.<-≤-trans
    (NatP.n<1+n 10)
    (NatP.m≤m+n 11 6)

fixedWidthQuotedRootAboveTen :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  10
  <
  Size.formulaNodeCount
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
fixedWidthQuotedRootAboveTen code codec =
  NatP.<-≤-trans
    tenLessSeventeen
    (fixedWidthQuotedRootAtLeastSeventeen code codec)

------------------------------------------------------------------------
-- Zero-variable all-functions table has exactly two states and eight
-- represented evaluation cells.
------------------------------------------------------------------------

fixedWidthReferenceStateCountExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Candidate.stateCount
    (Reference.referenceCandidate
      (Fixed.fixedWidthCandidateQuotedState code codec))
  ≡
  2
fixedWidthReferenceStateCountExact code codec
    rewrite
      Inert.fixedWidthCandidateQuotedRootVariableBoundZero
        code codec =
  refl

fixedWidthReferenceEvaluationCellCountExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Authority.arityTerminalEvaluationCellCount
    (Reference.referenceCandidate
      (Fixed.fixedWidthCandidateQuotedState code codec))
    (Reference.referenceAdmission
      (Fixed.fixedWidthCandidateQuotedState code codec))
  ≡
  8
fixedWidthReferenceEvaluationCellCountExact code codec
    rewrite
      Inert.fixedWidthCandidateQuotedRootVariableBoundZero
        code codec =
  refl

------------------------------------------------------------------------
-- Exact total reference charge on this root.
------------------------------------------------------------------------

fixedWidthReferenceTotalChargeExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Reference.referenceTotalCharge
    (Fixed.fixedWidthCandidateQuotedState code codec)
  ≡
  10
  +
  (Q2.programCodeSize
      (Fixed.fixedWidthCandidateQuotedState code codec)
    +
    Q2.rebindingOverhead
      (Fixed.fixedWidthCandidateQuotedState code codec))
fixedWidthReferenceTotalChargeExact code codec
    rewrite
      fixedWidthReferenceEvaluationCellCountExact code codec =
  refl

------------------------------------------------------------------------
-- Persistent payload cancels monotonically: the reference charge fits.
------------------------------------------------------------------------

fixedWidthReferenceChargeFits :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Reference.referenceTotalCharge
      (Fixed.fixedWidthCandidateQuotedState code codec)
  <
  Q2.recursiveMeasure
      (Fixed.fixedWidthCandidateQuotedState code codec)
fixedWidthReferenceChargeFits code codec
    rewrite
      fixedWidthReferenceTotalChargeExact code codec =
  NatP.+-monoʳ-<
    (Q2.programCodeSize state
      + Q2.rebindingOverhead state)
    (fixedWidthQuotedRootAboveTen code codec)
  where
    state : Q2.BoundedSelfReferenceState
    state =
      Fixed.fixedWidthCandidateQuotedState code codec

------------------------------------------------------------------------
-- B / first-step progress is now an exact theorem for the explicit reference
-- constructor on the present fixed-width quotation.
------------------------------------------------------------------------

fixedWidthReferenceConstructorProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Reference.referenceDirectDPConstructor
    (Fixed.fixedWidthCandidateQuotedState code codec)
  ≢
  Data.Maybe.Base.nothing
fixedWidthReferenceConstructorProgress code codec =
  Reference.referenceChargeFitGivesProgress
    (Fixed.fixedWidthCandidateQuotedState code codec)
    (fixedWidthReferenceChargeFits code codec)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- B is paid for the current fixed-width structural quotation by a fully
-- explicit transition table and finite semantic admission.
--
-- But SemanticInertnessExact simultaneously proves that same root is a
-- variable-free tautology.  Therefore this progress theorem cannot be promoted
-- to the missing opposite-SAT diagonal.  The surviving Clay wall is now the
-- semantics-bearing execution quotation itself.
------------------------------------------------------------------------
