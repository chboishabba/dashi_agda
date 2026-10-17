module DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact where

------------------------------------------------------------------------
-- STRUCTURALITY FIREWALL FOR THE RESOURCE-CLOSING COMPILER
--
-- ResourceClosingFixedProgramCompilation already exposes the real candidate
-- middle run, prefix/suffix phases and exact additive clock.  Its simulation
-- field, however, uses the generic semantic simulation interface whose `embed`
-- is an arbitrary meta-level function.
--
-- This owner keeps all existing same-object phase data and adds the missing
-- representation receipt: the simulation used by the resource compiler is
-- pointwise equal to a literal structural tape simulation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Opposite
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard

record StructuralResourceClosingFixedProgramCompilation
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (clocked : Clocked.PolynomiallyClockedStandardCandidate candidate) : Set₃ where
  field
    resource : Resource.ResourceClosingFixedProgramCompilation clocked

    structuralSimulation :
      Structural.StructuralStandardMachineSimulation
        (Presented.finitePresentedStandardMachine
          (Candidate.presentation (Clocked.standard clocked)))
        (Presented.finitePresentedStandardMachine
          (Opposite.presentation (Resource.fixed resource)))

    embedIsStructural :
      (configuration :
        Standard.StandardConfiguration
          (Presented.finitePresentedStandardMachine
            (Candidate.presentation (Clocked.standard clocked)))) →
      Simulation.embed
        (Resource.simulation resource)
        configuration
      ≡
      Simulation.embed
        (Structural.structuralToSimulation structuralSimulation)
        configuration

open StructuralResourceClosingFixedProgramCompilation public

structuralCandidateConfigurationSpanExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResourceClosingFixedProgramCompilation clocked)
    (configuration :
      Standard.StandardConfiguration
        (Presented.finitePresentedStandardMachine
          (Candidate.presentation (Clocked.standard clocked)))) →
  Structural.configurationSpan
    (Simulation.embed
      (Resource.simulation (resource structuralResource))
      configuration)
  ≡
  Structural.configurationSpan configuration
structuralCandidateConfigurationSpanExact structuralResource configuration
  rewrite embedIsStructural structuralResource configuration =
  Structural.structuralSimulationSpanExact
    (structuralSimulation structuralResource)
    configuration

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The candidate subrun can no longer be embedded by an arbitrary meta-level
-- configuration transformer.  Its state and tape symbols are represented
-- pointwise and its represented tape span is preserved exactly.
--
-- This still does not construct the self-quotation prefix.  It removes a
-- hidden representation-expansion escape hatch before prefix lower bounds or
-- quotation-generation theorems are attached.
------------------------------------------------------------------------
