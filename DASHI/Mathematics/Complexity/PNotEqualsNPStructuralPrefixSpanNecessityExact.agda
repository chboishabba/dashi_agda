module DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixSpanNecessityExact where

------------------------------------------------------------------------
-- NECESSARY SPAN INEQUALITY FOR A STRUCTURAL SELF-QUOTATION PREFIX
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation
import DASHI.Mathematics.Complexity.StandardMachineSpanGrowthExact as SpanGrowth
import DASHI.Mathematics.Complexity.ConcreteTapeStandardProjectionSpanExact as ProjectionSpan
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural

candidateOwnFormula :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate} →
  StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked →
  Cook.BooleanFormula
candidateOwnFormula structuralResource =
  Opposite.fixedCookFormula
    (Resource.fixed (StructuralResource.resource structuralResource))

candidateOwnInput :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Input.InputWord
    (Candidate.candidateConcreteMachine (Clocked.standard clocked))
candidateOwnInput {clocked = clocked} structuralResource =
  Candidate.encodeFormula
    (Clocked.standard clocked)
    (candidateOwnFormula structuralResource)

candidateOwnSteps :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate} →
  StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked → Nat
candidateOwnSteps {clocked = clocked} structuralResource =
  Candidate.exactSteps
    (Clocked.standard clocked)
    (candidateOwnFormula structuralResource)

prefixEndpointSpanExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Structural.configurationSpan
    (Simulation.embed
      (Resource.simulation (StructuralResource.resource structuralResource))
      (Language.guardedStandardStart
        (candidateOwnInput structuralResource)
        (candidateOwnSteps structuralResource)))
  ≡
  Guard.guardedInitialCols
    (candidateOwnInput structuralResource)
    (candidateOwnSteps structuralResource)
prefixEndpointSpanExact structuralResource =
  trans
    (StructuralResource.structuralCandidateConfigurationSpanExact
      structuralResource
      (Language.guardedStandardStart
        (candidateOwnInput structuralResource)
        (candidateOwnSteps structuralResource)))
    (ProjectionSpan.guardedStandardStartSpanExact
      (candidateOwnInput structuralResource)
      (candidateOwnSteps structuralResource))

structuralPrefixSpanNecessity :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Guard.guardedInitialCols
      (candidateOwnInput structuralResource)
      (candidateOwnSteps structuralResource)
  ≤
  Guard.guardedInitialCols
      (Opposite.input
        (Resource.fixed
          (StructuralResource.resource structuralResource)))
      (Opposite.steps
        (Resource.fixed
          (StructuralResource.resource structuralResource)))
    + Resource.prefixSteps
        (StructuralResource.resource structuralResource)
structuralPrefixSpanNecessity structuralResource =
  subst
    (λ startSpan →
      Guard.guardedInitialCols
          (candidateOwnInput structuralResource)
          (candidateOwnSteps structuralResource)
      ≤ startSpan
        + Resource.prefixSteps
            (StructuralResource.resource structuralResource))
    (ProjectionSpan.guardedStandardStartSpanExact
      (Opposite.input (Resource.fixed base))
      (Opposite.steps (Resource.fixed base)))
    (subst
      (λ endSpan →
        endSpan
        ≤ Structural.configurationSpan
            (Language.guardedStandardStart
              (Opposite.input (Resource.fixed base))
              (Opposite.steps (Resource.fixed base)))
          + Resource.prefixSteps base)
      (sym (prefixEndpointSpanExact structuralResource))
      (SpanGrowth.standardRunSpanBound (Resource.prefix base)))
  where
    base = StructuralResource.resource structuralResource

------------------------------------------------------------------------
-- INTERPRETATION
--
-- The target begins with a guarded seed row already padded by 2*T blanks.
-- Therefore represented span alone need not obstruct self-quotation: the blank
-- reserve can be larger than the candidate's embedded input span. The live
-- residual is information/content generation inside that span, not hidden tape
-- expansion.
------------------------------------------------------------------------
