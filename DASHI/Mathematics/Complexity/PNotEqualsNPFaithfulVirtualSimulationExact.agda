module DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualSimulationExact where

------------------------------------------------------------------------
-- FAITHFUL MACHINE-STATE OUTPUT THROUGH THE ENTIRE VIRTUAL SIMULATION
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (just)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as Frontier
import DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualGeneratorOutputExact as Output
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact as Semantics
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

record FaithfulEmbeddedGeneratedQueryCall
    {description presentation generator before after}
    (faithful : Output.FaithfulGeneratorOutput
      {presentation = presentation} generator)
    (call : Frontier.EmbeddedGeneratedQueryCall
      description {presentation} generator before after) : Set where
  field
    finalGeneratorStateIsBit :
      Standard.state
        (Frontier.finishConfiguration generator
          (Description.atIndex
            description
            (Frontier.index (Frontier.query call))))
      ≡
      Output.outputState faithful
        (just (Frontier.bit (Frontier.query call)))

open FaithfulEmbeddedGeneratedQueryCall public

faithfulCallGivesSemanticQuery :
  ∀ {description presentation generator before after}
    {faithful : Output.FaithfulGeneratorOutput
      {presentation = presentation} generator}
    {call : Frontier.EmbeddedGeneratedQueryCall
      description {presentation} generator before after} →
  FaithfulEmbeddedGeneratedQueryCall faithful call →
  Semantics.queryAnswer
    (Description.atIndex
      description
      (Frontier.index (Frontier.query call)))
  ≡ just (Frontier.bit (Frontier.query call))
faithfulCallGivesSemanticQuery faithfulCall =
  Output.faithfulSuccessfulQueryAnswerExact
    record
      { Output.finalStateIsBit =
          finalGeneratorStateIsBit faithfulCall
      }

data FaithfulGeneratedQueryChain
    {description presentation generator}
    (faithful : Output.FaithfulGeneratorOutput
      {presentation = presentation} generator) :
    ∀ {steps start finish} →
    Frontier.EmbeddedGeneratedQueryChain
      description {presentation} generator steps start finish →
    Set where

  faithfulChainDone :
    ∀ {configuration} →
    FaithfulGeneratedQueryChain faithful
      (Frontier.generatedChainDone {configuration = configuration})

  faithfulChainStep :
    ∀ {restSteps start middle finish}
      {call : Frontier.EmbeddedGeneratedQueryCall
        description generator start middle}
      {rest : Frontier.EmbeddedGeneratedQueryChain
        description generator restSteps middle finish} →
    FaithfulEmbeddedGeneratedQueryCall faithful call →
    FaithfulGeneratedQueryChain faithful rest →
    FaithfulGeneratedQueryChain faithful
      (Frontier.generatedChainStep call rest)

record FaithfulVirtualStep
    {SourceState SourceSymbol sourceMachine description targetPresentation generator
      sourceBefore sourceAfter targetBefore targetAfter}
    (faithful : Output.FaithfulGeneratorOutput
      {presentation = targetPresentation} generator)
    (step : Frontier.VirtualStepSimulation
      {SourceState} {SourceSymbol} {sourceMachine}
      description {targetPresentation} generator
      sourceBefore sourceAfter targetBefore targetAfter) : Set where
  field
    faithfulQueries :
      FaithfulGeneratedQueryChain faithful (Frontier.queryChain step)

open FaithfulVirtualStep public

data FaithfulVirtualRun
    {SourceState SourceSymbol sourceMachine description targetPresentation generator}
    (faithful : Output.FaithfulGeneratorOutput
      {presentation = targetPresentation} generator) :
    ∀ {sourceSteps sourceStart sourceFinish targetStart targetFinish}
      {sourceRun : Run.StandardExactRun
        sourceMachine sourceSteps sourceStart sourceFinish} →
    Frontier.VirtualRunSimulation
      {SourceState} {SourceSymbol} {sourceMachine}
      description {targetPresentation} generator
      sourceRun targetStart targetFinish →
    Set where

  faithfulVirtualDone :
    ∀ {sourceConfiguration targetConfiguration} →
    FaithfulVirtualRun faithful
      (Frontier.virtualRunDone
        {sourceConfiguration = sourceConfiguration}
        {targetConfiguration = targetConfiguration})

  faithfulVirtualStep :
    ∀ {sourceSteps sourceCurrent sourceNext sourceFinish targetCurrent targetNext targetFinish}
      {sourceRest : Run.StandardExactRun
        sourceMachine sourceSteps sourceNext sourceFinish}
      {step : Frontier.VirtualStepSimulation
        description generator
        sourceCurrent sourceNext targetCurrent targetNext}
      {rest : Frontier.VirtualRunSimulation
        description generator sourceRest targetNext targetFinish} →
    FaithfulVirtualStep faithful step →
    FaithfulVirtualRun faithful rest →
    FaithfulVirtualRun faithful
      (Frontier.virtualRunStep step rest)

record FaithfulVirtualSelfQuotationCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : Clocked.PolynomiallyClockedStandardCandidate candidate) : Set₃ where
  field
    base : Frontier.VirtualSelfQuotationCompilation clocked

    faithfulGenerator :
      Output.FaithfulGeneratorOutput
        (Frontier.universalGenerator base)

    faithfulCandidateSimulation :
      FaithfulVirtualRun
        faithfulGenerator
        (Frontier.candidateSimulation base)

open FaithfulVirtualSelfQuotationCompilation public
