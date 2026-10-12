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
-- Successful generated query on one immutable Cook description.
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
-- An ACTUAL same-target generator call: setup ; generator ; resume.
------------------------------------------------------------------------

record EmbeddedGeneratedQueryCall
    (description : Description.GuardedCookFormulaDescription)
    {presentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator presentation)
    (before after :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine presentation)) : Set₂ where
  field
    query : SuccessfulGeneratedQuery description generator

    setupSteps : Nat
    resumeSteps : Nat

    setupRun :
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        setupSteps
        before
        (Language.guardedStandardStart
          (Query.mapBoolSymbols
            (zeroSymbol generator)
            (oneSymbol generator)
            (Query.queryBits
              (Description.atIndex description (index query))))
          (querySteps generator
            (Description.atIndex description (index query))))

    resumeRun :
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine presentation)
        resumeSteps
        (finishConfiguration generator
          (Description.atIndex description (index query)))
        after

open EmbeddedGeneratedQueryCall public

embeddedCallSteps :
  ∀ {description presentation generator before after} →
  EmbeddedGeneratedQueryCall
    description {presentation} generator before after → Nat
embeddedCallSteps {generator = generator} call =
  (setupSteps call
    + querySteps generator
        (Description.atIndex _ (index (query call))))
  + resumeSteps call

------------------------------------------------------------------------
-- A chain is literal phase composition on the same target transition system.
------------------------------------------------------------------------

data EmbeddedGeneratedQueryChain
    (description : Description.GuardedCookFormulaDescription)
    {presentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator presentation) :
    Nat →
    Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine presentation) →
    Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine presentation) →
    Set₂ where

  generatedChainDone :
    ∀ {configuration} →
    EmbeddedGeneratedQueryChain
      description generator zero configuration configuration

  generatedChainStep :
    ∀ {callSteps restSteps start middle finish}
      (call :
        EmbeddedGeneratedQueryCall
          description generator start middle) →
    embeddedCallSteps call ≡ callSteps →
    EmbeddedGeneratedQueryChain
      description generator restSteps middle finish →
    EmbeddedGeneratedQueryChain
      description generator (callSteps + restSteps) start finish

------------------------------------------------------------------------
-- One source edge -> same-target query chain + actual core target run.
------------------------------------------------------------------------

record VirtualStepSimulation
    {SourceState SourceSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    (description : Description.GuardedCookFormulaDescription)
    {targetPresentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator targetPresentation)
    (sourceBefore sourceAfter : Standard.StandardConfiguration sourceMachine)
    (targetBefore targetAfter :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine targetPresentation)) : Set₂ where
  field
    sourceEdge :
      Standard.standardNext sourceMachine sourceBefore ≡ just sourceAfter

    queryStepsTotal : Nat
    afterQueries :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine targetPresentation)

    queryChain :
      EmbeddedGeneratedQueryChain
        description generator queryStepsTotal targetBefore afterQueries

    coreSteps : Nat
    coreRun :
      Run.StandardExactRun
        (Presented.finitePresentedStandardMachine targetPresentation)
        coreSteps afterQueries targetAfter

open VirtualStepSimulation public

virtualStepTotal :
  ∀ {SourceState SourceSymbol sourceMachine description targetPresentation generator
      sourceBefore sourceAfter targetBefore targetAfter} →
  VirtualStepSimulation
    {SourceState} {SourceSymbol} {sourceMachine}
    description {targetPresentation} generator
    sourceBefore sourceAfter targetBefore targetAfter → Nat
virtualStepTotal step =
  queryStepsTotal step + coreSteps step

data VirtualRunSimulation
    {SourceState SourceSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    (description : Description.GuardedCookFormulaDescription)
    {targetPresentation : Presented.FinitePresentedStandardTM}
    (generator : UniversalGuardedCookBitGenerator targetPresentation) :
    ∀ {sourceSteps sourceStart sourceFinish}
      (sourceRun :
        Run.StandardExactRun
          sourceMachine sourceSteps sourceStart sourceFinish) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine targetPresentation) →
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine targetPresentation) →
      Set₂ where

  virtualRunDone :
    ∀ {sourceConfiguration targetConfiguration} →
    VirtualRunSimulation
      description generator
      (Run.standardRunDone {configuration = sourceConfiguration})
      targetConfiguration targetConfiguration

  virtualRunStep :
    ∀ {sourceSteps sourceCurrent sourceNext sourceFinish}
      {targetCurrent targetNext targetFinish}
      {sourceRest :
        Run.StandardExactRun
          sourceMachine sourceSteps sourceNext sourceFinish}
      (step :
        VirtualStepSimulation
          description generator
          sourceCurrent sourceNext targetCurrent targetNext) →
    VirtualRunSimulation
      description generator sourceRest targetNext targetFinish →
    VirtualRunSimulation
      description generator
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
        (Candidate.execution
          (Clocked.standard clocked)
          (Opposite.fixedCookFormula
            (CodedFixed.forgetCodedFixed codedFixed)))
        candidateTargetStart candidateTargetFinish

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
--   * guarded Cook description and exact virtual source are canonical;
--   * all reads vary only the index of one immutable description;
--   * generator execution is on the SAME fixed target transition system;
--   * each query is an actual setup ; generator ; resume chain, not a number.
--
-- LIVE constructive obligations:
--   1. construct one coded target with generator + candidate/opposite modes;
--   2. prove `UniversalGuardedCookBitGenerator` for its canonical query code;
--   3. establish a representation invariant making each `coreRun` simulate the
--      corresponding source edge, with query calls exactly at virtual reads;
--   4. concatenate the per-edge target runs, then finite setup + negation suffix,
--      and close the SAME exact Cook budget;
--   5. reuse existing Cook iff / opposite-decision failure plumbing.
------------------------------------------------------------------------
