module DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact where

------------------------------------------------------------------------
-- ACTIVE FRONTIER AFTER THE LITERAL-MATERIALISATION NO-GO
--
-- Same-object corrections in this recut:
--   * the fixed opposite target is born as CodedFiniteStandardTM;
--   * its guarded Cook description and virtual source are canonical;
--   * every read varies only the index of that immutable description;
--   * read cost is canonical query-code length + universal-generator execution,
--     not the cheaper extensional List lookup used only for specification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

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
-- Charged trace for ONE immutable Cook description.
------------------------------------------------------------------------

record SuccessfulGeneratedQuery
    (description : Description.GuardedCookFormulaDescription)
    (generator : UniversalGuardedCookBitGenerator) : Set where
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
  Description.GuardedCookFormulaDescription →
  UniversalGuardedCookBitGenerator → Set
GeneratedQueryTrace description generator =
  List (SuccessfulGeneratedQuery description generator)

generatedTraceWork :
  ∀ {description generator} →
  GeneratedQueryTrace description generator → Nat
generatedTraceWork [] = zero
generatedTraceWork {description} {generator} (query ∷ rest) =
  queryCharge generator
    (Description.atIndex description (index query))
  + generatedTraceWork rest

record GeneratedQueryCostReceipt
    (description : Description.GuardedCookFormulaDescription)
    (generator : UniversalGuardedCookBitGenerator)
    (targetSteps : Nat) : Set where
  field
    trace : GeneratedQueryTrace description generator
    generatedWorkFitsTarget :
      generatedTraceWork trace ≤ targetSteps

open GeneratedQueryCostReceipt public

------------------------------------------------------------------------
-- Every successful generated read is also an exact canonical-source read.
------------------------------------------------------------------------

generatedQuerySound :
  ∀ {description generator}
    (query : SuccessfulGeneratedQuery description generator) →
  Virtual.BitAt
    (index query)
    (Binary.encodeFormulaBits (Description.formula description))
    (bit query)
generatedQuerySound {description} {generator} query
  rewrite Description.atIndexFormulaExact
    description (index query) =
  outputSound generator (outputExact query)

------------------------------------------------------------------------
-- One source edge -> finite target segment + fully charged generated reads.
------------------------------------------------------------------------

record VirtualStepSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {targetMachine : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (description : Description.GuardedCookFormulaDescription)
    (generator : UniversalGuardedCookBitGenerator)
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
    (generator : UniversalGuardedCookBitGenerator) :
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
      description generator
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
          description generator
          sourceCurrent sourceNext
          targetCurrent targetNext) →
    VirtualRunSimulation
      description generator sourceRest targetNext targetFinish →
    VirtualRunSimulation
      description generator
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
    codedFixed :
      CodedFixed.CodedFixedStandardOppositeMachine
        (Candidate.standardCandidateToCodeRealization
          (Clocked.standard clocked))

    universalGenerator : UniversalGuardedCookBitGenerator

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
--   * same fixed target is now low-universe coded syntax;
--   * actual guarded Cook description derived definitionally from that code;
--   * canonical exact virtual source derived with no oracle witness;
--   * all reads vary only the index of one immutable description;
--   * target-step receipts charge query serialization + generator execution.
--
-- LIVE constructive obligations:
--   1. inhabit ONE `UniversalGuardedCookBitGenerator` for `queryAnswer`;
--   2. build the stepwise target interpreter `VirtualRunSimulation` so its
--      generated trace corresponds to the source machine's actual input reads;
--   3. reattach finite setup + negation suffix + exact total target clock;
--   4. reuse existing Cook iff / opposite-decision failure plumbing.
------------------------------------------------------------------------
