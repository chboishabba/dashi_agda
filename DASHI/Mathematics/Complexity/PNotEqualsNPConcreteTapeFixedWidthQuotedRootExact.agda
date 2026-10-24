module DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeFixedWidthQuotedRootExact where

------------------------------------------------------------------------
-- LITERAL CONCRETE-TAPE BITS -> EXISTING FIXED-WIDTH QUOTED ROOT
--
-- CandidateDeterministicTapeCode now exposes its exact static program as a
-- fixed-width CNF bit vector.  Therefore the remaining codec input of
-- PNotEqualsNPFixedWidthCandidateQuotedRootExact is the identity codec.
--
-- This owner pays that representation seam directly; no semantic SAT claim is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateDeterministicTapeCodeExact as Tape
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as ProgramCode
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF

------------------------------------------------------------------------
-- Identity codec on the literal machine-program bits.
------------------------------------------------------------------------

tapeCodeCodec :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  CodeQuote.FixedWidthCandidateCodeCodec
    (Actual.CandidateCodeRealization.CandidateCode
      (Tape.candidateTapeToCodeRealization tape))
tapeCodeCodec tape = record
  { CodeQuote.width =
      ProgramCode.StaticProgramBitsWidth
        (Tape.machine tape)
  ; CodeQuote.encode =
      λ bits → bits
  ; CodeQuote.decode =
      λ bits → bits
  ; CodeQuote.decodeEncode =
      λ bits → refl
  }

------------------------------------------------------------------------
-- Exact same-object root for one concrete tape candidate.
------------------------------------------------------------------------

tapeFixedWidthQuotedState :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  Q2.BoundedSelfReferenceState
tapeFixedWidthQuotedState tape =
  Fixed.fixedWidthCandidateQuotedState
    (Tape.candidateTapeToCodeRealization tape)
    (tapeCodeCodec tape)

tapeFixedWidthCurrentFormulaExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  Q2.currentFormula (tapeFixedWidthQuotedState tape)
  ≡
  Q2.currentFormula
    (Fixed.fixedWidthCandidateQuotedState
      (Tape.candidateTapeToCodeRealization tape)
      (tapeCodeCodec tape))
tapeFixedWidthCurrentFormulaExact tape =
  refl

tapeFixedWidthProgramCodeSizeExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  Q2.programCodeSize (tapeFixedWidthQuotedState tape)
  ≡
  Tape.candidateProgramBitSize tape
tapeFixedWidthProgramCodeSizeExact tape =
  Fixed.fixedWidthCandidateQuotedProgramCodeSizeExact
    (Tape.candidateTapeToCodeRealization tape)
    (tapeCodeCodec tape)

TapeFixedWidthFirstStepProgress :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (tape : Tape.CandidateDeterministicTapeCode candidate) →
  DirectDP.DirectDPChargedStateConstructor →
  Set
TapeFixedWidthFirstStepProgress tape constructor =
  Fixed.FixedWidthCandidateQuotedFirstStepProgress
    (Tape.candidateTapeToCodeRealization tape)
    (tapeCodeCodec tape)
    constructor

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- A concrete deterministic tape candidate now supplies, without any extra
-- quotation parameter:
--   literal fixed-width code bits;
--   exact static code size;
--   injective structural Cook quotation;
--   the existing candidate-aware same-object Q2 root.
--
-- The structural quotation remains intentionally distinct from the semantic
-- Cook--Levin quotation used by the opposite diagonal.
------------------------------------------------------------------------
