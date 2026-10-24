module DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthQuotedRootSemanticInertnessExact where

------------------------------------------------------------------------
-- FIXED-WIDTH SELF-CODE QUOTATION IS SAT-SEMANTICALLY INERT
--
-- The candidate-aware finite fixed point on master is operationally genuine:
-- the fixed program runs D on the quotation of that same fixed program.
--
-- But the current structural quotation is only a syntax/provenance encoding.
-- Candidate-code bits are embedded as constant-only tautologies, and every
-- Program constructor tag is also built only from Boolean constants.
--
-- This owner proves exactly:
--
--   formulaVariableBound(root) = 0
--   evaluate(root, assignment) = true for EVERY assignment
--   hence root is satisfiable independently of D's answer.
--
-- Therefore operational self-application cannot be promoted to opposite-SAT
-- diagonal semantics. A future Clay-critical quotation must encode execution
-- semantics, not merely carry injective program syntax.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateQuotedSelfApplicationExact as SelfQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Quote
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2

------------------------------------------------------------------------
-- Constant-only candidate code quotation has no Cook variables.
------------------------------------------------------------------------

embedBitsVariableBoundZero :
  ∀ {width : Nat}
    (bits : CNF.Bits width) →
  Bridge.formulaVariableBound
    (Quote.embedBitsAsTautology bits)
  ≡
  zero
embedBitsVariableBoundZero CNF.[]ᵇ =
  refl
embedBitsVariableBoundZero (bit CNF.∷ᵇ rest)
    rewrite embedBitsVariableBoundZero rest =
  refl

fixedWidthCodeQuoteVariableBoundZero :
  ∀ {CandidateCode : Set}
    (codec : CodeQuote.FixedWidthCandidateCodeCodec CandidateCode)
    (code : CandidateCode) →
  Bridge.formulaVariableBound
    (CodeQuote.quoteCandidateCode codec code)
  ≡
  zero
fixedWidthCodeQuoteVariableBoundZero codec code =
  embedBitsVariableBoundZero
    (CodeQuote.encode codec code)

------------------------------------------------------------------------
-- Structural Program quotation preserves zero-variable syntax.
------------------------------------------------------------------------

structuralProgramQuoteVariableBoundZero :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (codeQuotation : SelfQuote.CandidateCodeFormulaQuotation code) →
  ((candidateCode : Actual.CandidateCodeRealization.CandidateCode code) →
    Bridge.formulaVariableBound
      (SelfQuote.quoteCandidateCode codeQuotation candidateCode)
    ≡ zero) →
  (program : Code.Program (SelfQuote.CandidateQuotedPrimitive code)) →
  Bridge.formulaVariableBound
    (SelfQuote.structuralProgramQuote codeQuotation program)
  ≡ zero
structuralProgramQuoteVariableBoundZero
    codeQuotation
    codeBound
    (Code.primitive SelfQuote.runCandidateOnQuote)
    rewrite
      codeBound
        (Actual.CandidateCodeRealization.candidateCode code) =
  refl
structuralProgramQuoteVariableBoundZero
    codeQuotation
    codeBound
    (Code.specialized program static)
    rewrite
      structuralProgramQuoteVariableBoundZero
        codeQuotation codeBound program
    | structuralProgramQuoteVariableBoundZero
        codeQuotation codeBound static =
  refl
structuralProgramQuoteVariableBoundZero
    codeQuotation
    codeBound
    (Code.diagonalized program)
    rewrite
      structuralProgramQuoteVariableBoundZero
        codeQuotation codeBound program =
  refl

------------------------------------------------------------------------
-- Fixed-width specialization: exact candidate-aware fixed point has arity 0.
------------------------------------------------------------------------

fixedWidthStructuralProgramQuoteVariableBoundZero :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code))
    (program : Code.Program (SelfQuote.CandidateQuotedPrimitive code)) →
  Bridge.formulaVariableBound
    (SelfQuote.structuralProgramQuote
      (Fixed.fixedWidthCandidateCodeQuotation code codec)
      program)
  ≡ zero
fixedWidthStructuralProgramQuoteVariableBoundZero code codec program =
  structuralProgramQuoteVariableBoundZero
    (Fixed.fixedWidthCandidateCodeQuotation code codec)
    (fixedWidthCodeQuoteVariableBoundZero codec)
    program

fixedWidthCandidateQuotedRootVariableBoundZero :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Bridge.formulaVariableBound
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
  ≡ zero
fixedWidthCandidateQuotedRootVariableBoundZero code codec =
  fixedWidthStructuralProgramQuoteVariableBoundZero
    code
    codec
    (SelfQuote.candidateQuotedFixedPointProgram code)

------------------------------------------------------------------------
-- Candidate-code bit quotation is tautological.
------------------------------------------------------------------------

fixedWidthCodeQuoteIsTautology :
  ∀ {CandidateCode : Set}
    (codec : CodeQuote.FixedWidthCandidateCodeCodec CandidateCode)
    (code : CandidateCode)
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (CodeQuote.quoteCandidateCode codec code)
    assignment
  ≡ true
fixedWidthCodeQuoteIsTautology codec code assignment =
  Quote.embedBitsIsTautology
    (CodeQuote.encode codec code)
    assignment

------------------------------------------------------------------------
-- Every structural program quotation is tautological whenever its embedded
-- candidate-code quotation is tautological.
------------------------------------------------------------------------

structuralProgramQuoteIsTautology :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (codeQuotation : SelfQuote.CandidateCodeFormulaQuotation code) →
  ((candidateCode : Actual.CandidateCodeRealization.CandidateCode code) →
    (assignment : Cook.Assignment) →
    Cook.evaluate
      (SelfQuote.quoteCandidateCode codeQuotation candidateCode)
      assignment
    ≡ true) →
  (program : Code.Program (SelfQuote.CandidateQuotedPrimitive code)) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
    (SelfQuote.structuralProgramQuote codeQuotation program)
    assignment
  ≡ true
structuralProgramQuoteIsTautology
    codeQuotation
    codeTautology
    (Code.primitive SelfQuote.runCandidateOnQuote)
    assignment
    rewrite
      codeTautology
        (Actual.CandidateCodeRealization.candidateCode code)
        assignment =
  refl
structuralProgramQuoteIsTautology
    codeQuotation
    codeTautology
    (Code.specialized program static)
    assignment
    rewrite
      structuralProgramQuoteIsTautology
        codeQuotation codeTautology program assignment
    | structuralProgramQuoteIsTautology
        codeQuotation codeTautology static assignment =
  refl
structuralProgramQuoteIsTautology
    codeQuotation
    codeTautology
    (Code.diagonalized program)
    assignment
    rewrite
      structuralProgramQuoteIsTautology
        codeQuotation codeTautology program assignment =
  refl

fixedWidthCandidateQuotedRootIsTautology :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code))
    (assignment : Cook.Assignment) →
  Cook.evaluate
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
    assignment
  ≡ true
fixedWidthCandidateQuotedRootIsTautology code codec assignment =
  structuralProgramQuoteIsTautology
    (Fixed.fixedWidthCandidateCodeQuotation code codec)
    (fixedWidthCodeQuoteIsTautology codec)
    (SelfQuote.candidateQuotedFixedPointProgram code)
    assignment

fixedWidthCandidateQuotedRootIsSatisfiable :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (Actual.CandidateCodeRealization.CandidateCode code)) →
  Cook.Satisfiable
    (Q2.currentFormula
      (Fixed.fixedWidthCandidateQuotedState code codec))
fixedWidthCandidateQuotedRootIsSatisfiable code codec =
  Cook.satisfyingAssignment
    (λ index → false)
    (fixedWidthCandidateQuotedRootIsTautology
      code codec (λ index → false))

------------------------------------------------------------------------
-- Exact firewall against the missing diagonal promotion.
--
-- The current quotation is SAT-true for every candidate code and every fixed
-- program. Candidate execution can return either Bool; that result does not
-- alter the quotation's SAT truth.
------------------------------------------------------------------------

data StructuralQuotationTruthDependsOnCandidateDecision : Set where

currentStructuralQuotationDoesNotEncodeOppositeDecision :
  StructuralQuotationTruthDependsOnCandidateDecision →
  ⊥
currentStructuralQuotationDoesNotEncodeOppositeDecision ()

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Operational same-object self-application is paid, but its present quotation
-- is variable-free and tautological. The true Clay-facing missing object is a
-- semantics-bearing computation quotation (e.g. a Cook-Levin execution
-- formula) whose SAT truth is tied to the candidate's own execution in the
-- required opposite polarity, with honest resource accounting.
------------------------------------------------------------------------
