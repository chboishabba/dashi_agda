module DASHI.Mathematics.Complexity.PNotEqualsNPFixedProgramStandardCompilerExact where

------------------------------------------------------------------------
-- PAID PARTIAL FIXED PROGRAM -> FINITE STANDARD-TM COMPILER BOUNDARY
--
-- FiniteSelfSpecializingCodeExact / PartialKleeneFixedPointExact already pay
-- the classical behavioral self-reference theorem. FixedOppositeSemantic-
-- QuotationExact specializes that finite program so, for any supplied formula,
-- its abstract run is definitionally:
--
--   just (not (D formula)).
--
-- The remaining execution theorem is therefore not another fixed-point axiom.
-- It is a compiler/resource theorem: realize THAT fixed finite computation as
-- one finite-presented conventional standard TM whose guarded Cook formula is
-- fed back as the formula parameter, and prove exact terminating execution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe.Base using (just)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPOppositeSemanticProgramQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedOppositeSemanticQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as StandardOpposite
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as StandardRun
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

------------------------------------------------------------------------
-- The actual remaining compiler output.
------------------------------------------------------------------------

record FixedProgramStandardCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set₂ where
  field
    fixed : StandardOpposite.FixedStandardOppositeMachine code

    finish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))

    execution :
      StandardRun.StandardExactRun
        (Presented.finitePresentedStandardMachine
          (StandardOpposite.presentation fixed))
        (StandardOpposite.steps fixed)
        (Language.guardedStandardStart
          (StandardOpposite.input fixed)
          (StandardOpposite.steps fixed))
        finish

    -- This is the exact compiler-correctness equation. Since the left side is
    -- `just`, it also pays termination of the compiled fixed computation.
    executionSemanticsExact :
      just
        (Local.decideEqual
          (Presented.finiteState
            (StandardOpposite.presentation fixed))
          (Standard.state finish)
          (Presented.acceptingState
            (StandardOpposite.presentation fixed)))
      ≡
      Fixed.fixedRun
        code
        (StandardOpposite.fixedCookFormula fixed)

open FixedProgramStandardCompilation public

------------------------------------------------------------------------
-- Compiler correctness immediately yields the singular opposite endpoint law.
------------------------------------------------------------------------

compilationGivesOppositeEndpoint :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate} →
  FixedProgramStandardCompilation code →
  StandardOpposite.FixedStandardOppositeEndpointRealization code
compilationGivesOppositeEndpoint
    {candidate = candidate}
    {code = code}
    compilation = record
  { StandardOpposite.fixed = fixed compilation
  ; StandardOpposite.finish = finish compilation
  ; StandardOpposite.execution = execution compilation
  ; StandardOpposite.endpointDecisionExact = endpointExact
  }
  where
    ownFormula : Cook.BooleanFormula
    ownFormula =
      StandardOpposite.fixedCookFormula (fixed compilation)

    endpointExact :
      Local.decideEqual
        (Presented.finiteState
          (StandardOpposite.presentation (fixed compilation)))
        (Standard.state (finish compilation))
        (Presented.acceptingState
          (StandardOpposite.presentation (fixed compilation)))
      ≡
      Opposite.notBool (Direct.decide candidate ownFormula)
    endpointExact =
      Candidate.justInjective
        (trans
          (executionSemanticsExact compilation)
          (Fixed.fixedRunExact code ownFormula))

------------------------------------------------------------------------
-- Hence the compiler alone is sufficient for the SAT error theorem.
------------------------------------------------------------------------

fixedProgramCompilationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) →
  FixedProgramStandardCompilation code →
  Direct.SATDecisionFailure candidate
fixedProgramCompilationGivesDecisionFailure code compilation =
  StandardOpposite.standardEndpointRealizationGivesDecisionFailure
    code
    (compilationGivesOppositeEndpoint compilation)

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- Classical self-reference is already paid in the abstract finite code layer.
-- The singular remaining diagonal implementation theorem is now exactly:
--
--   compile the already-paid fixed opposite finite computation
--     into one finite-presented standard TM
--   + construct its exact terminating guarded run
--   + prove final-control semantics equals the abstract fixed run when the
--     parameter is that same machine's guarded Cook formula.
--
-- This compiler theorem includes the resource-closing/termination obligation;
-- a partial recursion theorem by itself cannot inhabit it.
------------------------------------------------------------------------
