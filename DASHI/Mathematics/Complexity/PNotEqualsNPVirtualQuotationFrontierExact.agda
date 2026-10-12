module DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact where

------------------------------------------------------------------------
-- ACTIVE FRONTIER AFTER THE LITERAL-MATERIALISATION NO-GO
--
-- The former three-phase route required the prefix to write the complete binary
-- own Cook formula before D started.  The coded/structural no-go proves this
-- impossible for anchored candidates at positive resource budget.
--
-- The surviving architecture is VIRTUAL quotation:
--
--   compact Cook description + index
--        -> finite indexed bit generator
--        -> charged query trace
--        -> stepwise candidate simulation
--        -> opposite decision suffix.
--
-- This file defines the producer interfaces only.  It does not inhabit them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.CodedStandardPolynomialCostModelExact as Cost
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralResourceCompilerAnchoredNoGoExact as LiteralNoGo
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact as LiteralBudget
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource

import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual
import DASHI.Mathematics.Complexity.VirtualFormulaQueryTraceExact as Trace
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

------------------------------------------------------------------------
-- Re-export the architectural no-go at the new boundary.
------------------------------------------------------------------------

literalAnchoredRouteClosed :
  (closure : Cost.CodedStandardCostClosure)
  (anchored :
    Direct.AnchoredPolynomialSATDeciderCandidate
      (Cost.codedStandardPolynomialCostModel closure)) →
  StructuralResource.StructuralResourceClosingFixedProgramCompilation
    (LiteralBudget.codedClockedCandidate
      closure (Direct.candidate anchored)) →
  ⊥
literalAnchoredRouteClosed =
  LiteralNoGo.anchoredLiteralStructuralResourceImpossible

------------------------------------------------------------------------
-- Producer 1: finite indexed generator for the ACTUAL Cook bitstream.
--
-- `semanticSource` is only the extensional specification.  The executable data
-- are a finite standard machine, an encoded query input, an exact run, and a
-- polynomial clock.  A successful query's final bit must equal the specified
-- virtual source bit at that index.
------------------------------------------------------------------------

record FiniteIndexedBitGenerator
    (formula : Cook.BooleanFormula)
    (semanticSource : Virtual.VirtualFormulaBitSource formula) : Set₃ where
  field
    presentation : Presented.FinitePresentedStandardTM

    QueryInput : Set
    encodeQuery : Nat → QueryInput

    querySteps : Nat → Nat
    queryCoefficient : Nat
    queryDegree : Nat

    startConfiguration :
      QueryInput →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    finishConfiguration :
      (index : Nat) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    execution :
      (index : Nat) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        (querySteps index)
        (startConfiguration (encodeQuery index))
        (finishConfiguration index)

    outputBit :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation) →
      Bool

    outputExact :
      ∀ {index bit} →
      Virtual.readBit semanticSource index ≡ just bit →
      outputBit (finishConfiguration index) ≡ bit

    queryStepsPolynomial :
      (index : Nat) →
      querySteps index
      ≤ Virtual.queryPolynomialBudget
          queryCoefficient queryDegree formula index

open FiniteIndexedBitGenerator public

------------------------------------------------------------------------
-- Producer 2: one source-machine edge simulated by a finite target segment,
-- with every virtual-input query exposed and charged inside that segment.
------------------------------------------------------------------------

record VirtualStepSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {targetMachine : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    {formula : Cook.BooleanFormula}
    (bitSource : Virtual.VirtualFormulaBitSource formula)
    (sourceBefore sourceAfter : Standard.StandardConfiguration sourceMachine)
    (targetBefore targetAfter : Standard.StandardConfiguration targetMachine) : Set₂ where
  field
    sourceEdge :
      Standard.standardNext sourceMachine sourceBefore ≡ just sourceAfter

    targetSteps : Nat
    targetRun :
      Run.StandardExactRun
        targetMachine targetSteps targetBefore targetAfter

    queryCost :
      Trace.QueryTraceCostReceipt bitSource targetSteps

open VirtualStepSimulation public

------------------------------------------------------------------------
-- Stepwise run simulation: unlike the former arbitrary `embed`, this exposes a
-- finite target segment and charged query trace for EACH actual source edge.
------------------------------------------------------------------------

data VirtualRunSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {targetMachine : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    {formula : Cook.BooleanFormula}
    (bitSource : Virtual.VirtualFormulaBitSource formula) :
    ∀ {sourceSteps sourceStart sourceFinish}
      (sourceRun :
        Run.StandardExactRun
          sourceMachine sourceSteps sourceStart sourceFinish) →
      Standard.StandardConfiguration targetMachine →
      Standard.StandardConfiguration targetMachine →
      Set₂ where

  virtualRunDone :
    ∀ {sourceConfiguration targetConfiguration} →
    VirtualRunSimulation
      bitSource
      (Run.standardRunDone {configuration = sourceConfiguration})
      targetConfiguration
      targetConfiguration

  virtualRunStep :
    ∀ {sourceSteps sourceCurrent sourceNext sourceFinish}
      {targetCurrent targetNext targetFinish}
      {sourceEdge}
      {sourceRest :
        Run.StandardExactRun
          sourceMachine sourceSteps sourceNext sourceFinish} →
    VirtualStepSimulation
      bitSource
      sourceCurrent sourceNext
      targetCurrent targetNext →
    VirtualRunSimulation bitSource sourceRest targetNext targetFinish →
    VirtualRunSimulation
      bitSource
      (Run.standardRunStep sourceEdge sourceRest)
      targetCurrent
      targetFinish

------------------------------------------------------------------------
-- Active compiler boundary for one candidate.
--
-- The source run is the candidate's genuine exact run on the extensional own
-- formula.  The target does NOT structurally embed/materialise that source tape;
-- it simulates the run through the indexed source above.
------------------------------------------------------------------------

record VirtualSelfQuotationCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : Clocked.PolynomiallyClockedStandardCandidate candidate) : Set₃ where
  field
    fixed :
      Opposite.FixedStandardOppositeMachine
        (Candidate.standardCandidateToCodeRealization
          (Clocked.standard clocked))

    virtualSource :
      Virtual.DescribedVirtualFormulaBitSource
        (Opposite.fixedCookFormula fixed)

    indexedGenerator :
      FiniteIndexedBitGenerator
        (Opposite.fixedCookFormula fixed)
        (Virtual.source virtualSource)

    candidateTargetStart :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Opposite.presentation fixed))

    candidateTargetFinish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Opposite.presentation fixed))

    candidateSimulation :
      VirtualRunSimulation
        (Virtual.source virtualSource)
        (Candidate.execution
          (Clocked.standard clocked)
          (Opposite.fixedCookFormula fixed))
        candidateTargetStart
        candidateTargetFinish

    -- Prefix/suffix/total-clock compilation remains to be attached, but no full
    -- formula-materialisation premise is permitted in this replacement record.

open VirtualSelfQuotationCompilation public

------------------------------------------------------------------------
-- EXACT NEW FRONTIER
--
-- 1. Construct `FiniteIndexedBitGenerator` for the literal guarded Cook
--    constructor from compact machine/input/T description.
-- 2. Construct a finite target/interpreter and `VirtualRunSimulation` for the
--    candidate's exact own-formula run, paying every indexed read in target time.
-- 3. Reattach finite setup + negation suffix + exact total clock, then reuse the
--    already-paid Cook iff / opposite-decision failure plumbing.
--
-- The full encoded own formula must never be a free intermediate object in the
-- target-machine execution path; the anchored no-go above rules that route out.
------------------------------------------------------------------------
