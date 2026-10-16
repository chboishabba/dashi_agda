module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingResourceClosingTerminalExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED SAT CANDIDATE -> TERMINAL RESOURCE-CLOSING CUT
--
-- This owner removes all now-mechanical adapters from the terminal theorem.
-- Starting from one actual-halting coded SAT candidate:
--   * guarded Cook execution is constructed automatically;
--   * the legacy standard/polynomially-clocked candidate is derived automatically;
--   * the legacy candidate-code socket is bound to the literal actual machine;
--   * one ResourceClosingFixedProgramCompilation is then sufficient for a
--     concrete SATDecisionFailure and therefore the existing P != NP closure.
--
-- The remaining premise is intentionally strong and honest: it is the real
-- fixed-target prefix/setup + candidate + suffix + exact resource closure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateBridgeExact as HaltingBridge
import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCandidateCodeRealizationExact as CodeBinding
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedProgramStandardCompilerExact as Compiler

------------------------------------------------------------------------
-- 1. One actual-halting witness determines the legacy clocked candidate.
------------------------------------------------------------------------

haltingClockedCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Halting.CodedStandardHaltingPolynomialDecider
    (Direct.decide candidate) →
  DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact.PolynomiallyClockedStandardCandidate
    candidate
haltingClockedCandidate =
  HaltingBridge.haltingWitnessToPolynomiallyClockedCandidateAutomatic

------------------------------------------------------------------------
-- 2. Terminal resource compiler -> SAT decision failure.
------------------------------------------------------------------------

haltingResourceCompilationGivesDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (witness :
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)) →
  Resource.ResourceClosingFixedProgramCompilation
    (haltingClockedCandidate witness) →
  Direct.SATDecisionFailure candidate
haltingResourceCompilationGivesDecisionFailure
    {candidate = candidate}
    witness
    resource =
  Compiler.fixedProgramCompilationGivesDecisionFailure
    (DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact.standardCandidateToCodeRealization
      (DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact.standard
        (haltingClockedCandidate witness)))
    (Resource.resourceClosingToFixedProgramCompilation resource)

------------------------------------------------------------------------
-- 3. Universal actual-halting producer -> existing Clay-level core.
------------------------------------------------------------------------

record UniversalHaltingResourceCompiler
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₃ where
  field
    codedCandidate :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Halting.CodedStandardHaltingPolynomialDecider
        (Direct.decide candidate)

    resourceCompilation :
      (candidate : Direct.PolynomialSATDeciderCandidate cost) →
      Resource.ResourceClosingFixedProgramCompilation
        (haltingClockedCandidate (codedCandidate candidate))

open UniversalHaltingResourceCompiler public

universalHaltingResourceGivesUniversalFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalHaltingResourceCompiler cost →
  Direct.UniversalPolynomialSATDecisionFailure cost
universalHaltingResourceGivesUniversalFailure producer candidate =
  haltingResourceCompilationGivesDecisionFailure
    (codedCandidate producer candidate)
    (resourceCompilation producer candidate)

haltingResourceCompilationGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalHaltingResourceCompiler cost →
  Clay.PNotEqualsNP
haltingResourceCompilationGivesPNotEqualsNP producer =
  Clay.satLowerBoundProducerClosesClayCore
    (universalHaltingResourceGivesUniversalFailure producer)

------------------------------------------------------------------------
-- 4. Max-cut boundary.
------------------------------------------------------------------------

record HaltingResourceTerminalBoundary : Set where
  constructor halting-resource-terminal-boundary
  field
    actualCandidateCodeBound : Bool
    guardedCookTransportAutomatic : Bool
    actualRuntimeDistinctFromPolynomialUpperBound : Bool
    abstractKleeneFixedPointAlreadyPaid : Bool
    terminalLogicAfterResourceCompilerPaid : Bool
    resourceClosingCompilationStillRequired : Bool
    pNotEqualsNPClaimedWithoutResourceCompilation : Bool

canonicalHaltingResourceTerminalBoundary : HaltingResourceTerminalBoundary
canonicalHaltingResourceTerminalBoundary =
  halting-resource-terminal-boundary
    true true true true true true false

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The P != NP programme no longer has independent candidate-code, guarded-input,
-- Cook-semantic, endpoint-negation or terminal-logic leaves.  The singular live
-- construction is `ResourceClosingFixedProgramCompilation` for the automatically
-- derived actual-halting candidate: construct the fixed target prefix/setup,
-- route the candidate on that target's own Cook formula, append the opposite
-- suffix, and close the exact total resource accounting on that same target.
------------------------------------------------------------------------
