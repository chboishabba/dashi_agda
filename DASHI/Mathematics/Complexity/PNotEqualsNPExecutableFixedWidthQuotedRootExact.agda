module DASHI.Mathematics.Complexity.PNotEqualsNPExecutableFixedWidthQuotedRootExact where

------------------------------------------------------------------------
-- EXECUTABLE POLYNOMIAL SAT WITNESS -> FIXED-WIDTH SAME-OBJECT ROOT
--
-- This composes the already-paid representation layers:
--
--   ExecutablePolynomialTimeDecider
--      -> CandidateCodeRealization
--      + FixedWidthCandidateCodeCodec
--      -> injective Cook quotation
--      -> literal finite self-application root.
--
-- No code extraction from the old extensional PolynomialCostModel occurs.
-- The executable refinement carries code by construction; the only additional
-- representation input is a fixed-width codec for that concrete code type.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPExecutablePolynomialCostRefinementExact as ExecCost
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateCodeFormulaQuotationExact as CodeQuote
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedWidthCandidateQuotedRootExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP

------------------------------------------------------------------------
-- Candidate induced by one executable polynomial witness.
------------------------------------------------------------------------

ExecutableSATCandidate :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecCost.ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool} →
  ExecCost.ExecutablePolynomialTimeDecider base decider →
  Direct.PolynomialSATDeciderCandidate
    (ExecCost.executablePolynomialCostModel base closure)
ExecutableSATCandidate witness =
  Direct.polynomial-sat-decider-candidate
    _
    witness

executableCandidateCode :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecCost.ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool}
    (witness : ExecCost.ExecutablePolynomialTimeDecider base decider) →
  Actual.CandidateCodeRealization
    (ExecutableSATCandidate {closure = closure} witness)
executableCandidateCode witness =
  ExecCost.candidateCodeRealizationFromExecutableWitness witness

------------------------------------------------------------------------
-- Exact code carrier on this realization.
------------------------------------------------------------------------

ExecutableCandidateCodeType :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecCost.ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool} →
  ExecCost.ExecutablePolynomialTimeDecider base decider →
  Set
ExecutableCandidateCodeType witness =
  Actual.CandidateCodeRealization.CandidateCode
    (executableCandidateCode witness)

------------------------------------------------------------------------
-- Canonical candidate-aware state once a fixed-width codec is supplied.
------------------------------------------------------------------------

executableFixedWidthQuotedState :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecCost.ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool}
    (witness : ExecCost.ExecutablePolynomialTimeDecider base decider) →
  CodeQuote.FixedWidthCandidateCodeCodec
    (ExecutableCandidateCodeType witness) →
  Q2.BoundedSelfReferenceState
executableFixedWidthQuotedState witness codec =
  Fixed.fixedWidthCandidateQuotedState
    (executableCandidateCode witness)
    codec

------------------------------------------------------------------------
-- Progress target on the exact executable same-object root.
------------------------------------------------------------------------

ExecutableFixedWidthFirstStepProgress :
  ∀ {base : PR.PolynomialCostModel Cook.BooleanFormula}
    {closure : ExecCost.ExecutableCodeClosure Cook.BooleanFormula}
    {decider : Cook.BooleanFormula → Bool}
    (witness : ExecCost.ExecutablePolynomialTimeDecider base decider)
    (codec :
      CodeQuote.FixedWidthCandidateCodeCodec
        (ExecutableCandidateCodeType witness)) →
  DirectDP.DirectDPChargedStateConstructor →
  Set
ExecutableFixedWidthFirstStepProgress witness codec constructor =
  Fixed.FixedWidthCandidateQuotedFirstStepProgress
    (executableCandidateCode witness)
    codec
    constructor

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- In the executable cost refinement, candidate code -> same-object quoted root
-- is now a direct composition.  The remaining representation input is exactly
-- a fixed-width codec for the concrete executable code type.
--
-- The mathematical residual is unchanged and explicit:
--   prove the direct-DP constructor must make one successful first step at
--   this exact state, without assuming SAT correctness/failure semantics.
------------------------------------------------------------------------
