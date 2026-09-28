module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateAwareFinitePrimitiveExact where

------------------------------------------------------------------------
-- CANDIDATE-AWARE FINITE PRIMITIVE
--
-- A0 supplies CandidateCodeRealization:
--
--   c_D
--   runCandidateCode c_D phi = decide D phi.
--
-- The old Q2 primitive ignored its quoted program and never invoked D.  This
-- module adds the smallest honest candidate-aware finite primitive surface:
--
--   runCandidateDecision
--   runBoundedDescent
--
-- with a tagged output type so the same finite-code calculus can execute both
-- decision and formula-producing instructions.
--
-- This pays "the self-reference machinery can literally consume c_D".  It does
-- NOT yet compile the decision result into the diagonal Boolean formula phi_D.
-- That formula compiler is exposed as the remaining A1 seam below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Maybe.Base using (Maybe; nothing; just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact as Exec
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual

------------------------------------------------------------------------
-- Tagged outputs.
------------------------------------------------------------------------

data CandidateAwareOutput : Set where
  decisionOutput :
    Bool →
    CandidateAwareOutput

  formulaOutput :
    Cook.BooleanFormula →
    CandidateAwareOutput

------------------------------------------------------------------------
-- Literal finite primitive syntax parameterized by the exact candidate-code
-- carrier.
------------------------------------------------------------------------

data CandidateAwarePrimitive
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (code : Actual.CandidateCodeRealization candidate) : Set where

  runCandidateDecision :
    Actual.CandidateCodeRealization.CandidateCode code →
    Cook.BooleanFormula →
    CandidateAwarePrimitive code

  runBoundedDescent :
    CandidateAwarePrimitive code

------------------------------------------------------------------------
-- Primitive semantics.
--
-- Input is unit because runCandidateDecision closes over the exact formula it
-- evaluates.  The quoted finite program is accepted by the binary interpreter
-- shape but is not needed for the candidate instruction itself.
------------------------------------------------------------------------

candidateAwarePrimitiveSemantics :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  Code.PrimitiveSemantics
    (CandidateAwarePrimitive candidateCode)
    ⊤
    CandidateAwareOutput
candidateAwarePrimitiveSemantics
    candidateCode
    stepSystem
    initial =
  record
    { Code.runPrimitive1 =
        runUnary
    ; Code.runPrimitive2 =
        runBinary
    }
  where
    runUnary :
      CandidateAwarePrimitive candidateCode →
      ⊤ →
      Maybe CandidateAwareOutput
    runUnary
        (runCandidateDecision code formula)
        input =
      just
        (decisionOutput
          (Actual.CandidateCodeRealization.runCandidateCode
            candidateCode
            code
            formula))
    runUnary runBoundedDescent input =
      nothing

    runBinary :
      CandidateAwarePrimitive candidateCode →
      Code.Program (CandidateAwarePrimitive candidateCode) →
      ⊤ →
      Maybe CandidateAwareOutput
    runBinary
        (runCandidateDecision code formula)
        quoted
        input =
      just
        (decisionOutput
          (Actual.CandidateCodeRealization.runCandidateCode
            candidateCode
            code
            formula))
    runBinary
        runBoundedDescent
        quoted
        input =
      just
        (formulaOutput
          (Exec.canonicalTerminalFormula
            stepSystem
            initial))

------------------------------------------------------------------------
-- Same-object candidate execution theorem.
------------------------------------------------------------------------

candidateAwarePrimitiveRunsExactDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState)
    (formula : Cook.BooleanFormula) →
  Code.runPrimitive1
      (candidateAwarePrimitiveSemantics
        candidateCode
        stepSystem
        initial)
      (runCandidateDecision
        (Actual.CandidateCodeRealization.candidateCode candidateCode)
        formula)
      tt
  ≡
  just
    (decisionOutput
      (Direct.decide candidate formula))
candidateAwarePrimitiveRunsExactDecision
    candidateCode
    stepSystem
    initial
    formula
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        candidateCode
        formula =
  refl

candidateAwareBinaryPrimitiveRunsExactDecision :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState)
    (formula : Cook.BooleanFormula)
    (quoted :
      Code.Program
        (CandidateAwarePrimitive candidateCode)) →
  Code.runPrimitive2
      (candidateAwarePrimitiveSemantics
        candidateCode
        stepSystem
        initial)
      (runCandidateDecision
        (Actual.CandidateCodeRealization.candidateCode candidateCode)
        formula)
      quoted
      tt
  ≡
  just
    (decisionOutput
      (Direct.decide candidate formula))
candidateAwareBinaryPrimitiveRunsExactDecision
    candidateCode
    stepSystem
    initial
    formula
    quoted
    rewrite
      Actual.CandidateCodeRealization.codeDecisionExact
        candidateCode
        formula =
  refl

------------------------------------------------------------------------
-- Literal finite self-specializing system that now contains D as executable
-- syntax rather than merely as an external semantic parameter.
------------------------------------------------------------------------

candidateAwarePartialSystem :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  _
candidateAwarePartialSystem
    candidateCode
    stepSystem
    initial =
  Code.finiteCodePartialSystem
    (candidateAwarePrimitiveSemantics
      candidateCode
      stepSystem
      initial)

candidateAwareDiagonalCompiler :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  _
candidateAwareDiagonalCompiler
    candidateCode
    stepSystem
    initial =
  Code.finiteCodeDiagonalCompiler
    (candidateAwarePrimitiveSemantics
      candidateCode
      stepSystem
      initial)

------------------------------------------------------------------------
-- A1 remaining formula compiler.
--
-- The candidate is now actually executable inside the finite code calculus.
-- What is still missing is a syntax constructor which converts candidate
-- execution/self-quotation into the exact initial Cook formula phi_D.
--
-- Keep that requirement operational.  No SAT correctness field appears.
------------------------------------------------------------------------

record CandidateAwareInitialFormulaCompiler
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    compile :
      Actual.CandidateCodeRealization.CandidateCode candidateCode →
      Cook.BooleanFormula

    compiledFormula :
      Cook.BooleanFormula

    compiledFormulaExact :
      compiledFormula
      ≡
      compile
        (Actual.CandidateCodeRealization.candidateCode candidateCode)

open CandidateAwareInitialFormulaCompiler public

record CandidateAwareInitialState
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (candidateCode : Actual.CandidateCodeRealization candidate) : Set₁ where
  field
    compiler :
      CandidateAwareInitialFormulaCompiler candidateCode

    state :
      Q2.BoundedSelfReferenceState

    currentFormulaExact :
      Q2.currentFormula state
      ≡
      CandidateAwareInitialFormulaCompiler.compiledFormula compiler

    programCodeSizeExact :
      Q2.programCodeSize state
      ≡
      Actual.CandidateCodeRealization.codeSize candidateCode
        (Actual.CandidateCodeRealization.candidateCode candidateCode)

open CandidateAwareInitialState public

------------------------------------------------------------------------
-- FRONTIER
--
-- Paid:
--   c_D is executable inside literal finite self-specializing syntax;
--   execution agrees exactly with decide D.
--
-- Open A1:
--   build the specific candidate-aware formula compiler/self-instantiation body
--   and prove its output is currentFormula(s_D), with honest resource charges.
--
-- Open B:
--   prove the direct-DP constructor cannot stop on that exact s_D.
--
-- C remains already paid by the residual-width obstruction.
------------------------------------------------------------------------
