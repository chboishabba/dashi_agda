module DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixEndpointContentExact where

------------------------------------------------------------------------
-- THE REIFIED PREFIX ENDPOINT IS THE STRUCTURALLY MAPPED CANDIDATE INPUT ROW
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPPolynomiallyClockedStandardCandidateExact as Clocked
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingStandardCompilerExact as Resource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralResourceClosingCompilerExact as StructuralResource
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixSpanNecessityExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPStructuralPrefixConcreteWriteExact as ReifiedPrefix

import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeStandardReverseRunExact as Reverse
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalProjectionFlattenExact as ProjectionFlatten
import DASHI.Mathematics.Complexity.ConcreteTapeSymbolWriteLocalityExact as Writes
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Simulation
import DASHI.Mathematics.Complexity.StructuralStandardMachineSimulationExact as Structural
import DASHI.Mathematics.Complexity.StandardConfigurationFlattenExact as Flatten

prefixEndpointContentExact :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {clocked : Clocked.PolynomiallyClockedStandardCandidate candidate}
    (structuralResource :
      StructuralResource.StructuralResourceClosingFixedProgramCompilation clocked) →
  Writes.eraseRow
    (Reverse.finish
      (ReifiedPrefix.reified
        (ReifiedPrefix.reifyStructuralPrefix structuralResource)))
  ≡
  Structural.mapList
    (Structural.symbolMap
      (StructuralResource.structuralSimulation structuralResource))
    (Writes.eraseRow
      (Guard.guardedInitialRow
        (Prefix.candidateOwnInput structuralResource)
        (Prefix.candidateOwnSteps structuralResource)))
prefixEndpointContentExact {clocked = clocked} structuralResource =
  trans
    (sym
      (ProjectionFlatten.canonicalProjectionFlattenExact
        finalUnique))
    (trans
      (cong Flatten.flattenConfiguration finalProjection)
      (trans
        (cong Flatten.flattenConfiguration embedExact)
        (trans
          (Flatten.flattenStructuralEmbed
            (Structural.stateMap structural)
            (Structural.symbolMap structural)
            candidateStart)
          (cong
            (Structural.mapList (Structural.symbolMap structural))
            (ProjectionFlatten.canonicalProjectionFlattenExact
              candidateStartUnique)))))
  where
    base = StructuralResource.resource structuralResource
    structural = StructuralResource.structuralSimulation structuralResource

    reifiedPrefix =
      ReifiedPrefix.reified
        (ReifiedPrefix.reifyStructuralPrefix structuralResource)

    finalUnique = Reverse.finalUnique reifiedPrefix
    finalProjection = Reverse.finalProjection reifiedPrefix

    candidateInput = Prefix.candidateOwnInput structuralResource
    candidateSteps = Prefix.candidateOwnSteps structuralResource
    candidateStartUnique =
      Language.guardedInitialUnique candidateInput candidateSteps
    candidateStart =
      Language.guardedStandardStart candidateInput candidateSteps

    embedExact :
      Simulation.embed (Resource.simulation base) candidateStart
      ≡
      Simulation.embed
        (Structural.structuralToSimulation structural)
        candidateStart
    embedExact =
      StructuralResource.embedIsStructural
        structuralResource candidateStart

------------------------------------------------------------------------
-- CONTENT FRONTIER
--
-- The prefix write trace and endpoint are now on the same literal tape object:
-- the final concrete row contains exactly the pointwise structural image of the
-- candidate's guarded own-formula row.  Any lower bound can therefore count
-- which target symbols differ from the fixed guarded seed and compare that count
-- directly with prefixSteps.
------------------------------------------------------------------------
