module DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact where

------------------------------------------------------------------------
-- ACTIVE FRONTIER AFTER THE LITERAL-MATERIALISATION NO-GO
--
-- Same-object corrections in this recut:
--   * the fixed opposite target is born as CodedFiniteStandardTM;
--   * its guarded Cook description and virtual source are canonical;
--   * every read varies only the index of that immutable description;
--   * the universal bit generator EXECUTES ON THAT SAME fixed target machine;
--   * read cost is canonical query-code length + actual generator execution.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
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
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedFixedStandardOppositeExact as CodedFixed
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PolynomialClockArithmeticExact as Clock
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

import DASHI.Mathematics.Complexity.VirtualFormulaBitSourceExact as Virtual
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.CanonicalGuardedCookVirtualSourceExact as CanonicalGuarded
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
-- ONE universal bit generator, parameterised by the SAME target presentation.
------------------------------------------------------------------------

universalQueryPolynomialBudget :
  Nat → Nat → Query.GuardedCookBitQuery → Nat
universalQueryPolynomialBudget coefficient degree query =
  coefficient
  * Clock.natPower (suc (Query.queryBitLength query)) degree

record UniversalGuardedCookBitGenerator
    (presentation : Presented.FinitePresentedStandardTM) : Set₂ where
  field
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
  ∀ {presentation} →
  UniversalGuardedCookBitGenerator presentation →
  Query.GuardedCookBitQuery → Nat
queryCharge generator query =
  Query.queryBitLength query + querySteps generator query

------------------------------------------------------------------------
-- Charged trace for ONE immutable Cook description on ONE target machine.
------------------------------------------------------------------------

record SuccessfulGeneratedQuery
    (description : Description.GuardedCookFormulaDescription)
    {presentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator presentation) : Set where
  field
    index : Nat
    bit : Bool
    outputExact :
      outputBit generator
        (finishConfiguration generator
          (Description.atIndex description index))
      ≡ just bit

open SuccessfulGeneratedQuery public

GeneratedQueryTrace :
  (description : Description.GuardedCookFormulaDescription) →
  ∀ {presentation} →
  UniversalGuardedCookBitGenerator presentation → Set
GeneratedQueryTrace description generator =
  List (SuccessfulGeneratedQuery description generator)

generatedTraceWork :
  ∀ {description presentation}
    {generator : UniversalGuardedCookBitGenerator presentation} →
  GeneratedQueryTrace description generator → Nat
generatedTraceWork [] = zero
generatedTraceWork {description} {generator = generator} (query ∷ rest) =
  queryCharge generator
    (Description.atIndex description (index query))
  + generatedTraceWork rest

record GeneratedQueryCostReceipt
    (description : Description.GuardedCookFormulaDescription)
    {presentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator presentation)
    (targetSteps : Nat) : Set where
  field
    trace : GeneratedQueryTrace description generator
    generatedWorkFitsTarget :
      generatedTraceWork trace ≤ targetSteps

open GeneratedQueryCostReceipt public

generatedQuerySound :
  ∀ {description presentation}
    {generator : UniversalGuardedCookBitGenerator presentation}
    (query : SuccessfulGeneratedQuery description generator) →
  Virtual.BitAt
    (index query)
    (Binary.encodeFormulaBits (Description.formula description))
    (bit query)
generatedQuerySound {description} {generator = generator} query
  rewrite Description.atIndexFormulaExact
    description (index query) =
  outputSound generator (outputExact query)

------------------------------------------------------------------------
-- One source edge -> one same-target segment + charged same-target reads.
------------------------------------------------------------------------

record VirtualStepSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {targetMachine : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (description : Description.GuardedCookFormulaDescription)
    {targetPresentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator targetPresentation)
    (targetIsPresented :
      targetMachine
      ≡ Presented.finitePresentedStandardMachine targetPresentation)
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
      GeneratedQueryCostReceipt description generator targetSteps

open VirtualStepSimulation public

data VirtualRunSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {targetMachine : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (description : Description.GuardedCookFormulaDescription)
    {targetPresentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator targetPresentation)
    (targetIsPresented :
      targetMachine
      ≡ Presented.finitePresentedStandardMachine targetPresentation) :
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
      description generator targetIsPresented
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
          description generator targetIsPresented
          sourceCurrent sourceNext targetCurrent targetNext) →
    VirtualRunSimulation
      description generator targetIsPresented
      sourceRest targetNext targetFinish →
    VirtualRunSimulation
      description generator targetIsPresented
      (Run.standardRunStep
        (VirtualStepSimulation.sourceEdge step)
        sourceRest)
      targetCurrent targetFinish

------------------------------------------------------------------------
-- Candidate-specific virtual compilation boundary.
------------------------------------------------------------------------

record VirtualSelfQuotationCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : Clocked.PolynomiallyClockedStandardCandidate candidate) : Set₃ where
  field
    codedFixed :
      CodedFixed.CodedFixedStandardOppositeMachine
        (Candidate.standardCandidateToCodeRealization
          (Clocked.standard clocked))

    universalGenerator :
      UniversalGuardedCookBitGenerator
        (Opposite.presentation
          (CodedFixed.forgetCodedFixed codedFixed))

    candidateTargetStart :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Opposite.presentation
            (CodedFixed.forgetCodedFixed codedFixed)))

    candidateTargetFinish :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Opposite.presentation
            (CodedFixed.forgetCodedFixed codedFixed)))

    candidateSimulation :
      VirtualRunSimulation
        (CodedFixed.codedFixedDescription codedFixed)
        universalGenerator
        refl
        (Candidate.execution
          (Clocked.standard clocked)
          (Opposite.fixedCookFormula
            (CodedFixed.forgetCodedFixed codedFixed)))
        candidateTargetStart
        candidateTargetFinish

open VirtualSelfQuotationCompilation public

fixedOfVirtualCompilation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate} →
  VirtualSelfQuotationCompilation clocked →
  Opposite.FixedStandardOppositeMachine
    (Candidate.standardCandidateToCodeRealization
      (Clocked.standard clocked))
fixedOfVirtualCompilation compilation =
  CodedFixed.forgetCodedFixed (codedFixed compilation)

virtualSourceOfCompilation :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (compilation : VirtualSelfQuotationCompilation clocked) →
  Virtual.VirtualFormulaBitSource
    (Opposite.fixedCookFormula (fixedOfVirtualCompilation compilation))
virtualSourceOfCompilation compilation =
  CanonicalGuarded.canonicalGuardedSource
    (CodedFixed.codedFixedDescription (codedFixed compilation))

------------------------------------------------------------------------
-- EXACT NEW FRONTIER
--
-- PAID structurally:
--   * literal materialisation route closed for anchored candidates;
--   * same fixed target is low-universe coded syntax;
--   * actual guarded Cook description and exact virtual source are canonical;
--   * all reads vary only the index of one immutable description;
--   * the universal generator runs on the SAME fixed target transition system;
--   * target receipts charge query serialization + actual generator execution.
--
-- LIVE constructive obligations:
--   1. construct a coded fixed target whose own transition table contains the
--      universal guarded-Cook bit generator and opposite/candidate modes;
--   2. prove `UniversalGuardedCookBitGenerator` for that target;
--   3. build `VirtualRunSimulation`, with query phases actually concatenated
--      inside each target segment (not merely numerically charged);
--   4. reattach finite setup + negation suffix + exact total target clock and
--      reuse existing Cook iff / opposite-decision failure plumbing.
------------------------------------------------------------------------
