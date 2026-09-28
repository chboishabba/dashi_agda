module DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact where

------------------------------------------------------------------------
-- CANDIDATE / ACTUAL SELF-INSTANTIATION SAME-OBJECT BOUNDARY
--
-- The live P route needs more than a function D -> arbitrary bounded state.
--
-- Existing finite-code machinery really does construct a Kleene-style fixed
-- point, but the current Q2 primitive body is:
--
--   runBoundedDescent
--
-- and its binary primitive semantics ignores the quoted program completely.
-- Moreover PolynomialSATDeciderCandidate stores only
--
--   decide : BooleanFormula -> Bool
--   polynomialDecision : ...
--
-- with no finite executable program/code witness attached.
--
-- Therefore the current repository has two genuine objects:
--
--   * a polynomial SAT decision function D;
--   * a literal finite self-specializing Q2 program;
--
-- but no same-object theorem identifying D with code consumed by the latter.
--
-- This file makes that missing seam explicit and records only operational/code
-- equalities.  It introduces NO SAT correctness, opposite-SAT, or failure field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteCodeQ2ExecutionRealizationExact as Exec
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectDPChargedRecurrenceExact as DirectDP

------------------------------------------------------------------------
-- What the current actual finite-code path proves exactly.
------------------------------------------------------------------------

q2FixedPointSyntaxIsCandidateIndependent :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (stepSystem : Q2.BoundedSelfReferenceStepSystem)
    (initial : Q2.BoundedSelfReferenceState) →
  Exec.q2FixedPointProgram stepSystem initial
  ≡
  Code.primitiveBodyFixedPoint
    Exec.runBoundedDescent
q2FixedPointSyntaxIsCandidateIndependent
    candidate
    stepSystem
    initial =
  Exec.q2FixedPointIsLiteralFiniteCode
    stepSystem
    initial

q2PrimitiveExecutionErasesQuotedProgram :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem)
  (initial : Q2.BoundedSelfReferenceState)
  (left right : Code.Program Exec.Q2Primitive) →
  Code.runPrimitive2
      (Exec.q2PrimitiveSemantics stepSystem initial)
      Exec.runBoundedDescent
      left
      tt
  ≡
  Code.runPrimitive2
      (Exec.q2PrimitiveSemantics stepSystem initial)
      Exec.runBoundedDescent
      right
      tt
q2PrimitiveExecutionErasesQuotedProgram
    stepSystem
    initial
    left
    right =
  refl

q2PrimitiveExecutionIsCanonicalTerminalFormula :
  (stepSystem : Q2.BoundedSelfReferenceStepSystem)
  (initial : Q2.BoundedSelfReferenceState)
  (quoted : Code.Program Exec.Q2Primitive) →
  Code.runPrimitive2
      (Exec.q2PrimitiveSemantics stepSystem initial)
      Exec.runBoundedDescent
      quoted
      tt
  ≡
  just (Exec.canonicalTerminalFormula stepSystem initial)
q2PrimitiveExecutionIsCanonicalTerminalFormula
    stepSystem
    initial
    quoted =
  refl

------------------------------------------------------------------------
-- Exact same-object package still required.
--
-- CandidateCode is intentionally abstract here: the current
-- PolynomialSATDeciderCandidate interface does not supply one.
--
-- The important point is the shape of the missing bridge.  It binds the code
-- to the candidate's literal decision function and binds the bounded state's
-- accounting to that same code, without asserting that the candidate is right
-- or wrong on SAT.
------------------------------------------------------------------------

record CandidateCodeRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost) : Set₁ where
  field
    CandidateCode : Set

    candidateCode :
      CandidateCode

    runCandidateCode :
      CandidateCode →
      Cook.BooleanFormula →
      Bool

    codeDecisionExact :
      (formula : Cook.BooleanFormula) →
      runCandidateCode candidateCode formula
      ≡
      Direct.decide candidate formula

    codeSize :
      CandidateCode →
      Nat

open CandidateCodeRealization public

record CandidateInitialRootRealization
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    (candidate : Direct.PolynomialSATDeciderCandidate cost)
    (constructor : DirectDP.DirectDPChargedStateConstructor) : Set₁ where
  constructor candidate-initial-root-realization
  field
    code :
      CandidateCodeRealization candidate

    initial :
      Q2.BoundedSelfReferenceState

    -- The state uses the size of the exact code identified with D.
    programCodeMatchesCandidate :
      Q2.programCodeSize initial
      ≡
      CandidateCodeRealization.codeSize code
        (CandidateCodeRealization.candidateCode code)

    -- The Q2 step system is the literal direct-DP system whose first step will
    -- be audited.  No semantic SAT condition is attached.
    stepSystem :
      Q2.BoundedSelfReferenceStepSystem

    stepSystemIsDirectDP :
      stepSystem
      ≡
      DirectDP.directDPConstructorToQ2StepSystem constructor

    -- The actual finite-code fixed point is the literal repository
    -- specialization/diagonalization product for this exact Q2 system/state.
    fixedPointProgram :
      Code.Program Exec.Q2Primitive

    fixedPointProgramExact :
      fixedPointProgram
      ≡
      Exec.q2FixedPointProgram
        stepSystem
        initial

    fixedPointIsActualSelfSpecialization :
      fixedPointProgram
      ≡
      Code.primitiveBodyFixedPoint
        Exec.runBoundedDescent

open CandidateInitialRootRealization public

------------------------------------------------------------------------
-- The current finite-code path pays the self-specialization half of the future
-- realization automatically once a candidate-code binding and initial state
-- exist.  What it does NOT pay is the missing candidate-code witness itself or
-- any theorem saying currentFormula initial is generated from executing that
-- code.
------------------------------------------------------------------------

actualFiniteCodeFixedPointFor :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    (code : CandidateCodeRealization candidate)
    (initial : Q2.BoundedSelfReferenceState)
    (programCodeExact :
      Q2.programCodeSize initial
      ≡
      CandidateCodeRealization.codeSize code
        (CandidateCodeRealization.candidateCode code)) →
  CandidateInitialRootRealization
    candidate
    constructor
actualFiniteCodeFixedPointFor
    {constructor = constructor}
    code
    initial
    programCodeExact =
  candidate-initial-root-realization
    code
    initial
    programCodeExact
    (DirectDP.directDPConstructorToQ2StepSystem constructor)
    refl
    (Exec.q2FixedPointProgram
      (DirectDP.directDPConstructorToQ2StepSystem constructor)
      initial)
    refl
    (Exec.q2FixedPointIsLiteralFiniteCode
      (DirectDP.directDPConstructorToQ2StepSystem constructor)
      initial)

------------------------------------------------------------------------
-- Remaining same-object debt.
--
-- CandidateInitialRootRealization is STILL deliberately weaker than the final
-- desired object: currentFormula initial has not yet been proved to be produced
-- from the candidate code.  The current Q2 primitive cannot establish that,
-- because its quote argument is erased.
--
-- The next implementation target must therefore be an executable candidate
-- code carrier plus a candidate-aware self-instantiation primitive/body whose
-- output is identified with currentFormula initial.
------------------------------------------------------------------------

record CandidateGeneratedInitialFormula
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {constructor : DirectDP.DirectDPChargedStateConstructor}
    (realization :
      CandidateInitialRootRealization candidate constructor) : Set₁ where
  field
    generatedFormula :
      Cook.BooleanFormula

    generatedFromCandidateCode :
      Cook.BooleanFormula

    currentFormulaIsGenerated :
      Q2.currentFormula
        (CandidateInitialRootRealization.initial realization)
      ≡
      generatedFormula

    generatedFormulaIsCandidateComputation :
      generatedFormula
      ≡
      generatedFromCandidateCode

open CandidateGeneratedInitialFormula public

------------------------------------------------------------------------
-- Firewall/status.
------------------------------------------------------------------------

data CandidateSelfInstantiationCouplingStatus : Set where
  finiteSelfSpecializationPaid : CandidateSelfInstantiationCouplingStatus
  quotedProgramConsumedByQ2Primitive : CandidateSelfInstantiationCouplingStatus
  candidateExecutableCodeBound : CandidateSelfInstantiationCouplingStatus
  initialFormulaGeneratedFromCandidateCode : CandidateSelfInstantiationCouplingStatus

currentFiniteCodeCouplingStatus :
  CandidateSelfInstantiationCouplingStatus
currentFiniteCodeCouplingStatus =
  finiteSelfSpecializationPaid

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- A. first-step progress on the loose builder is candidate-erasing;
-- B. current finite-code self-specialization is real but candidate-erasing;
-- C. the next honest object is therefore:
--
--      candidate executable code
--        + exact code/decide agreement
--        + candidate-aware self-instantiation computation
--        + currentFormula initial = output of that computation
--        + exact resource accounting
--
-- with NO SAT correctness/error/opposite-semantics premise.
--
-- Only after this same-object object exists is first-step progress on s_D a
-- meaningful candidate-coupled theorem target.
------------------------------------------------------------------------
