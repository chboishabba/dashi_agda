module DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact where

------------------------------------------------------------------------
-- FIXED-WIDTH CANDIDATE CODE -> SAME-OBJECT QUOTED Q2 ROOT
--
-- This owner composes:
--
--   CandidateCodeRealization
--   + FixedWidthCandidateCodeCodec
--   + injective bit -> Cook quotation
--   + literal finite candidate self-application
--
-- into one exact root state.
--
-- The result is still representation / same-object infrastructure:
-- no SAT correctness, opposite-SAT semantics, decision failure, or progress
-- premise is included.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact as SelfQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width

------------------------------------------------------------------------
-- Canonical Cook quotation induced by the fixed-width candidate codec.
------------------------------------------------------------------------

fixedWidthCandidateCodeQuotation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  CodeQuote.FixedWidthCandidateCodeCodec
    (Actual.CandidateCodeRealization.CandidateCode code) →
  SelfQuote.CandidateCodeFormulaQuotation code
fixedWidthCandidateCodeQuotation code codec =
  record
    { SelfQuote.quoteCandidateCode =
        CodeQuote.quoteCandidateCode codec
    }

fixedWidthCandidateCodeQuotationInjective :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code))
    {left right :
      Actual.CandidateCodeRealization.CandidateCode code} →
  SelfQuote.quoteCandidateCode
      (fixedWidthCandidateCodeQuotation code codec)
      left
  ≡
  SelfQuote.quoteCandidateCode
      (fixedWidthCandidateCodeQuotation code codec)
      right →
  left ≡ right
fixedWidthCandidateCodeQuotationInjective
    code
    codec
    equality =
  CodeQuote.quoteCandidateCodeInjective
    codec
    equality

------------------------------------------------------------------------
-- Exact candidate-coupled root.
------------------------------------------------------------------------

fixedWidthCandidateQuotedState :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  CodeQuote.FixedWidthCandidateCodeCodec
    (Actual.CandidateCodeRealization.CandidateCode code) →
  Q2.BoundedSelfReferenceState
fixedWidthCandidateQuotedState code codec =
  SelfQuote.candidateQuotedSelfApplicationState
    code
    (fixedWidthCandidateCodeQuotation
      code
      codec)

fixedWidthCandidateQuotedCurrentFormulaExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Q2.currentFormula
    (fixedWidthCandidateQuotedState code codec)
  ≡
  SelfQuote.candidateQuotedFixedPointFormula
    code
    (SelfQuote.structuralProgramFormulaQuotation
      (fixedWidthCandidateCodeQuotation code codec))
fixedWidthCandidateQuotedCurrentFormulaExact code codec =
  refl

fixedWidthCandidateQuotedProgramCodeSizeExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Q2.programCodeSize
    (fixedWidthCandidateQuotedState code codec)
  ≡
  Actual.CandidateCodeRealization.codeSize
    code
    (Actual.CandidateCodeRealization.candidateCode code)
fixedWidthCandidateQuotedProgramCodeSizeExact code codec =
  refl

fixedWidthCandidateQuotedBudgetExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Q2.resourceBudget
    (fixedWidthCandidateQuotedState code codec)
  ≡
  Q2.recursiveMeasure
    (fixedWidthCandidateQuotedState code codec)
fixedWidthCandidateQuotedBudgetExact code codec =
  refl

fixedWidthCandidateQuotedRunsCandidateOnCurrentFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  SelfQuote.Code.run1
      (SelfQuote.candidateQuotedPrimitiveSemantics
        code
        (SelfQuote.structuralProgramFormulaQuotation
          (fixedWidthCandidateCodeQuotation code codec)))
      (SelfQuote.candidateQuotedFixedPointProgram code)
      Agda.Builtin.Unit.tt
  ≡
  Data.Maybe.Base.just
    (Direct.decide
      candidate
      (Q2.currentFormula
        (fixedWidthCandidateQuotedState code codec)))
fixedWidthCandidateQuotedRunsCandidateOnCurrentFormula
    code
    codec =
  SelfQuote.candidateQuotedStateRunsCandidateOnCurrentFormula
    code
    (fixedWidthCandidateCodeQuotation code codec)

------------------------------------------------------------------------
-- B on this fixed-width same-object root.
------------------------------------------------------------------------

FixedWidthCandidateQuotedFirstStepProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  CodeQuote.FixedWidthCandidateCodeCodec
    (Actual.CandidateCodeRealization.CandidateCode code) →
  DirectDP.DirectDPChargedStateConstructor →
  Set
FixedWidthCandidateQuotedFirstStepProgress
    code
    codec
    constructor =
  constructor
    (fixedWidthCandidateQuotedState code codec)
  ≢
  nothing

------------------------------------------------------------------------
-- C attacks the same state.
------------------------------------------------------------------------

fixedWidthCandidateQuotedHighWidthForcesStop :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code))
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (fixedWidthCandidateQuotedState code codec))}
    remaining
    width →
  Q2.recursiveMeasure
      (fixedWidthCandidateQuotedState code codec)
  ≤
  Width.triple width →
  constructor
      (fixedWidthCandidateQuotedState code codec)
  ≡
  nothing
fixedWidthCandidateQuotedHighWidthForcesStop
    code
    codec
    constructor
    witness
    measureBelowWidth =
  DirectDP.directDPHighWidthForcesConstructorStop
    witness
    measureBelowWidth
    constructor

fixedWidthCandidateQuotedWidthRefutesProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code))
    (constructor : DirectDP.DirectDPChargedStateConstructor)
    {remaining width : Nat} →
  Width.ResidualWidthWitness
    {root =
      Bridge.cookToIndexed
        (Q2.currentFormula
          (fixedWidthCandidateQuotedState code codec))}
    remaining
    width →
  Q2.recursiveMeasure
      (fixedWidthCandidateQuotedState code codec)
  ≤
  Width.triple width →
  FixedWidthCandidateQuotedFirstStepProgress
    code
    codec
    constructor →
  ⊥
fixedWidthCandidateQuotedWidthRefutesProgress
    code
    codec
    constructor
    witness
    measureBelowWidth
    progress =
  progress
    (fixedWidthCandidateQuotedHighWidthForcesStop
      code
      codec
      constructor
      witness
      measureBelowWidth)

------------------------------------------------------------------------
-- FRONTIER
--
-- A1 is now paid modulo exactly one standard representation input:
--
--   a fixed-width codec for the concrete executable candidate code.
--
-- Given that codec:
--
--   * candidate code is quoted injectively into Cook syntax;
--   * the literal finite fixed program consumes its own quotation;
--   * currentFormula(s_D) is definitionally that quotation;
--   * code/rebinding/resource accounting is exact;
--   * B and C are stated on the same state.
--
-- What remains genuinely mathematical is B:
--
--   constructor(s_D) != nothing.
--
-- A0c still needs a standard concrete machine model supplying the fixed-width
-- code codec and executable-cost-model coverage.
------------------------------------------------------------------------
