module DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact where

------------------------------------------------------------------------
-- ACTIVE FRONTIER AFTER THE LITERAL-MATERIALISATION NO-GO
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
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
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual
import DASHI.Mathematics.Complexity.VirtualFormulaQueryTraceExact as Trace
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

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
-- ONE universal finite bit generator for all canonical guarded-Cook queries.
------------------------------------------------------------------------

universalQueryPolynomialBudget :
  Nat → Nat → Query.GuardedCookBitQuery → Nat
universalQueryPolynomialBudget coefficient degree query =
  coefficient
  * Clock.natPower (suc (Query.queryBitLength query)) degree

record UniversalGuardedCookBitGenerator : Set₃ where
  field
    presentation : Presented.FinitePresentedStandardTM

    zeroSymbol : Presented.Symbol presentation
    oneSymbol : Presented.Symbol presentation
    binaryDistinct : zeroSymbol ≡ oneSymbol → ⊥
    zeroNotBlank : zeroSymbol ≡ Presented.blank presentation → ⊥
    oneNotBlank : oneSymbol ≡ Presented.blank presentation → ⊥

    querySteps : Query.GuardedCookBitQuery → Nat
    queryCoefficient : Nat
    queryDegree : Nat

    finishConfiguration :
      (query : Query.GuardedCookBitQuery) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)

    execution :
      (query : Query.GuardedCookBitQuery) →
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        (querySteps query)
        (Language.guardedStandardStart
          (Query.mapBoolSymbols
            zeroSymbol oneSymbol (Query.queryBits query))
          (querySteps query))
        (finishConfiguration query)

    outputBit :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation) →
      Maybe Bool

    outputSound :
      ∀ {query bit} →
      outputBit (finishConfiguration query) ≡ just bit →
      Virtual.BitAt
        (Query.index query)
        (Binary.encodeFormulaBits (Query.queryFormula query))
        bit

    outputComplete :
      ∀ {query bit} →
      Virtual.BitAt
        (Query.index query)
        (Binary.encodeFormulaBits (Query.queryFormula query))
        bit →
      outputBit (finishConfiguration query) ≡ just bit

    queryStepsPolynomial :
      (query : Query.GuardedCookBitQuery) →
      querySteps query
      ≤ universalQueryPolynomialBudget
          queryCoefficient queryDegree query

open UniversalGuardedCookBitGenerator public

queryCharge :
  UniversalGuardedCookBitGenerator →
  Query.GuardedCookBitQuery → Nat
queryCharge generator query =
  Query.queryBitLength query + querySteps generator query

------------------------------------------------------------------------
-- One source edge -> finite target segment + explicit charged virtual reads.
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
      {sourceRest :
        Run.StandardExactRun
          sourceMachine sourceSteps sourceNext sourceFinish}
      (step :
        VirtualStepSimulation
          bitSource
          sourceCurrent sourceNext
          targetCurrent targetNext) →
    VirtualRunSimulation bitSource sourceRest targetNext targetFinish →
    VirtualRunSimulation
      bitSource
      (Run.standardRunStep
        (VirtualStepSimulation.sourceEdge step)
        sourceRest)
      targetCurrent
      targetFinish

------------------------------------------------------------------------
-- Candidate-specific virtual compilation boundary.
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
      Virtual.VirtualFormulaBitSource
        (Opposite.fixedCookFormula fixed)

    -- One base description. All reads vary ONLY the index via Query.withIndex.
    baseQuery : Query.GuardedCookBitQuery

    baseQueryFormulaExact :
      Query.queryFormula baseQuery
      ≡ Opposite.fixedCookFormula fixed

    universalGenerator : UniversalGuardedCookBitGenerator

    generatorAgreesWithSource :
      (index : Nat) →
      outputBit universalGenerator
        (finishConfiguration universalGenerator
          (Query.withIndex baseQuery index))
      ≡ Virtual.readBit virtualSource index

    sourceQueryWorkExact :
      (index : Nat) →
      Virtual.queryWork virtualSource index
      ≡ queryCharge universalGenerator
          (Query.withIndex baseQuery index)

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
        virtualSource
        (Candidate.execution
          (Clocked.standard clocked)
          (Opposite.fixedCookFormula fixed))
        candidateTargetStart
        candidateTargetFinish

open VirtualSelfQuotationCompilation public

------------------------------------------------------------------------
-- EXACT NEW FRONTIER
--
-- 1. Implement ONE `UniversalGuardedCookBitGenerator` on canonical query code.
-- 2. Produce ONE compact `baseQuery` for the fixed target; every read is exactly
--    `withIndex baseQuery i`, so machine/input/T cannot vary with the answer.
-- 3. Build stepwise `VirtualRunSimulation`, paying query-code length + generator
--    execution for every read inside actual target-machine time.
-- 4. Reattach finite setup + negation suffix + exact total target clock and
--    reuse the already-paid Cook iff/opposite-decision plumbing.
--
-- Literal full-formula materialisation is no longer an admissible frontier.
------------------------------------------------------------------------
