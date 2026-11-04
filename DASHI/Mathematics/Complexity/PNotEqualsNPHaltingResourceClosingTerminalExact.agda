module DASHI.Mathematics.Complexity.PNotEqualsNPHaltingResourceClosingTerminalExact where

------------------------------------------------------------------------
-- ACTUAL-HALTING CODED SAT CANDIDATE -> TERMINAL RESOURCE-CLOSING CUT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact as Clay
import DASHI.Mathematics.Complexity.CodedStandardHaltingPolynomialDeciderExact as Halting
import DASHI.Mathematics.Complexity.PNotEqualsNPHaltingCodedCandidateBridgeExact as HaltingBridge
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedProgramStandardCompilerExact as Compiler

------------------------------------------------------------------------
-- 1. One actual-halting witness determines the existing clocked candidate.
------------------------------------------------------------------------

haltingClockedCandidate :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost} →
  Halting.CodedStandardHaltingPolynomialDecider
    (Direct.decide candidate) →
  Clocked.PolynomiallyClockedStandardCandidate candidate
haltingClockedCandidate =
  HaltingBridge.haltingWitnessToPolynomiallyClockedCandidateAutomatic

------------------------------------------------------------------------
-- 2. Terminal resource compiler -> concrete SAT decision failure.
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
    witness
    resource =
  Compiler.fixedProgramCompilationGivesDecisionFailure
    (Candidate.standardCandidateToCodeRealization
      (Clocked.standard (haltingClockedCandidate witness)))
    (Resource.resourceClosingToFixedProgramCompilation resource)

------------------------------------------------------------------------
-- 3. Universal actual-halting producer -> existing universal SAT failure.
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

universalHaltingResourceGivesSATLowerBoundProducer :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  UniversalHaltingResourceCompiler cost →
  Clay.SATLowerBoundProducer cost
universalHaltingResourceGivesSATLowerBoundProducer producer =
  Direct.universalDecisionFailureGivesSATLowerBoundProducer
    (universalHaltingResourceGivesUniversalFailure producer)

haltingResourceCompilationGivesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Clay.PNotEqualsNPEstablishedBackground cost →
  UniversalHaltingResourceCompiler cost →
  Clay.PNotEqualsNP cost
haltingResourceCompilationGivesPNotEqualsNP background producer =
  Direct.universalDecisionFailureClosesPNotEqualsNP
    background
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
-- The programme no longer has independent candidate-code, guarded-input,
-- Cook-semantic, endpoint-negation or terminal-logic leaves.  The singular live
-- construction is `ResourceClosingFixedProgramCompilation` for the automatically
-- derived actual-halting candidate: construct the fixed target prefix/setup,
-- route the candidate on that target's own Cook formula, append the opposite
-- suffix, and close the exact total resource accounting on that same target.
------------------------------------------------------------------------
