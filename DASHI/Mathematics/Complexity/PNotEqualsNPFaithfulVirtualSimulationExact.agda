module DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualSimulationExact where

------------------------------------------------------------------------
-- FAITHFUL MACHINE-STATE OUTPUT THROUGH THE ENTIRE VIRTUAL SIMULATION
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as Frontier
import DASHI.Mathematics.Complexity.PNotEqualsNPFaithfulVirtualGeneratorOutputExact as Output
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

------------------------------------------------------------------------
-- One embedded generator call really terminates in its declared bit state.
------------------------------------------------------------------------

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
          (DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact.atIndex
            description
            (Frontier.index (Frontier.query call))))
      ≡
      Output.outputState faithful
        (Agda.Builtin.Maybe.just
          (Frontier.bit (Frontier.query call)))

open FaithfulEmbeddedGeneratedQueryCall public

faithfulCallGivesSemanticQuery :
  ∀ {description presentation generator before after}
    {faithful : Output.FaithfulGeneratorOutput
      {presentation = presentation} generator}
    {call : Frontier.EmbeddedGeneratedQueryCall
      description {presentation} generator before after} →
  FaithfulEmbeddedGeneratedQueryCall faithful call →
  DASHI.Mathematics.Complexity.GuardedCookBitQuerySemanticsExact.queryAnswer
    (DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact.atIndex
      description
      (Frontier.index (Frontier.query call)))
  ≡
  Agda.Builtin.Maybe.just (Frontier.bit (Frontier.query call))
faithfulCallGivesSemanticQuery faithfulCall =
  Output.faithfulSuccessfulQueryAnswerExact
    record
      { Output.finalStateIsBit =
          finalGeneratorStateIsBit faithfulCall
      }

------------------------------------------------------------------------
-- Recursively require the same property for every call in every query chain.
------------------------------------------------------------------------

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
      {sourceRun : DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact.StandardExactRun
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
      {sourceRest : DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact.StandardExactRun
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

------------------------------------------------------------------------
-- Clay-critical active wrapper: the base compilation plus faithful machine-state
-- outputs for every generator call actually used in candidateSimulation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The active virtual route no longer depends on an unrestricted meta-level
-- observer to recover generated bits.  Every bit consumed by the simulated
-- candidate must be represented by the actual finite control state reached by
-- the same target machine's generator run.
------------------------------------------------------------------------
