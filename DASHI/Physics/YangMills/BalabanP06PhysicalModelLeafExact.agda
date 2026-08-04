module DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- fifth edition, Springer, 2017.
-- DOI: 10.1007/978-3-662-53622-3.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- Name the exact physical inhabitants needed to construct the repository's
-- P06ModelLeafDischargePackage.  Generic spanning-tree, DFS, walk-count and
-- recombination reducers are already owned elsewhere; this file prevents them
-- from being requested again as physical assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanP06FiniteNeighbourGraphExact as FiniteGraph
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PhysicalPolymerSupportAdapter : Set₁ where
  field
    graphAdapter : Entropy.BalabanGraphAdapter

    supportVerticesAreLiteralPolymerSupport : Set
    supportVerticesAreLiteralPolymerSupportEvidence :
      supportVerticesAreLiteralPolymerSupport

    supportRootBelongsToSupport : Set
    supportRootBelongsToSupportEvidence :
      supportRootBelongsToSupport

    supportHasNoDuplicatePhysicalBlocks : Set
    supportHasNoDuplicatePhysicalBlocksEvidence :
      supportHasNoDuplicatePhysicalBlocks

    physicalAdjacencyAgreesWithSupportGraph : Set
    physicalAdjacencyAgreesWithSupportGraphEvidence :
      physicalAdjacencyAgreesWithSupportGraph

open PhysicalPolymerSupportAdapter public

record ReducedSkeletonGeometryInputs
    (support : PhysicalPolymerSupportAdapter) : Set₁ where
  field
    reducedComplexity :
      Entropy.BalabanReducedSkeletonComplexityAdapter
        (graphAdapter support)

    branchVerticesSeparated : Set
    branchVerticesSeparatedEvidence : branchVerticesSeparated

    reducedSegmentsInternallyDisjoint : Set
    reducedSegmentsInternallyDisjointEvidence :
      reducedSegmentsInternallyDisjoint

    eachReducedSegmentPositiveLength : Set
    eachReducedSegmentPositiveLengthEvidence :
      eachReducedSegmentPositiveLength

    segmentCountControlledByBranchCount : Set
    segmentCountControlledByBranchCountEvidence :
      segmentCountControlledByBranchCount

    branchCountControlledByDiameter : Set
    branchCountControlledByDiameterEvidence :
      branchCountControlledByDiameter

open ReducedSkeletonGeometryInputs public

record PhysicalDecorationInputs
    (support : PhysicalPolymerSupportAdapter) : Set₁ where
  field
    decorationMultiplicity :
      Entropy.BalabanDecorationMultiplicityAdapter
        (graphAdapter support)

    localDecorationChoicesUniformlyBounded : Set
    localDecorationChoicesUniformlyBoundedEvidence :
      localDecorationChoicesUniformlyBounded

    decorationSupportOwnedBySkeletonVertex : Set
    decorationSupportOwnedBySkeletonVertexEvidence :
      decorationSupportOwnedBySkeletonVertex

    decorationEncodingInjective : Set
    decorationEncodingInjectiveEvidence :
      decorationEncodingInjective

    decorationWordLengthLinearInReducedComplexity : Set
    decorationWordLengthLinearInReducedComplexityEvidence :
      decorationWordLengthLinearInReducedComplexity

open PhysicalDecorationInputs public

record PhysicalPolymerDecompositionInputs
    (support : PhysicalPolymerSupportAdapter) : Set₁ where
  field
    decomposition :
      Entropy.BalabanPolymerDecompositionAdapter
        (graphAdapter support)

    polymerHasCanonicalReducedSkeleton : Set
    polymerHasCanonicalReducedSkeletonEvidence :
      polymerHasCanonicalReducedSkeleton

    polymerHasCanonicalDecoration : Set
    polymerHasCanonicalDecorationEvidence :
      polymerHasCanonicalDecoration

    decodeSkeletonDecoration : Set
    decodeSkeletonDecorationEvidence : decodeSkeletonDecoration

    decodeEncodePolymer : Set
    decodeEncodePolymerEvidence : decodeEncodePolymer

    encodePolymerInjectiveOrBoundedFibre : Set
    encodePolymerInjectiveOrBoundedFibreEvidence :
      encodePolymerInjectiveOrBoundedFibre

open PhysicalPolymerDecompositionInputs public

record P06PhysicalModelLeafInputs : Set₁ where
  field
    support : PhysicalPolymerSupportAdapter
    reducedSkeleton : ReducedSkeletonGeometryInputs support
    decorations : PhysicalDecorationInputs support
    decomposition : PhysicalPolymerDecompositionInputs support

    finiteRangeExponentialSummation :
      Entropy.LinearRangeExponentialSum

    concreteNeighbourGraph : FiniteGraph.FiniteNeighbourGraph
    concreteNeighbourGraphMatchesSupport : Set
    concreteNeighbourGraphMatchesSupportEvidence :
      concreteNeighbourGraphMatchesSupport

open P06PhysicalModelLeafInputs public

p06ModelLeafFromPhysicalInputs :
  P06PhysicalModelLeafInputs →
  Entropy.P06ModelLeafDischargePackage
p06ModelLeafFromPhysicalInputs inputs = record
  { Entropy.P06ModelLeafDischargePackage.graphAdapter =
      graphAdapter (support inputs)
  ; Entropy.P06ModelLeafDischargePackage.reducedSkeletonComplexityAdapter =
      reducedComplexity (reducedSkeleton inputs)
  ; Entropy.P06ModelLeafDischargePackage.decorationMultiplicityAdapter =
      decorationMultiplicity (decorations inputs)
  ; Entropy.P06ModelLeafDischargePackage.polymerDecompositionAdapter =
      decomposition (decomposition inputs)
  ; Entropy.P06ModelLeafDischargePackage.linearRangeSum =
      finiteRangeExponentialSummation inputs
  }

record P06PhysicalModelLeafReceipt
    (inputs : P06PhysicalModelLeafInputs) : Set₁ where
  field
    package : Entropy.P06ModelLeafDischargePackage
    packageIsCanonical :
      package ≡ p06ModelLeafFromPhysicalInputs inputs
    theoremBoundary : String

open P06PhysicalModelLeafReceipt public

p06PhysicalModelLeafReceipt :
  (inputs : P06PhysicalModelLeafInputs) →
  P06PhysicalModelLeafReceipt inputs
p06PhysicalModelLeafReceipt inputs = record
  { package = p06ModelLeafFromPhysicalInputs inputs
  ; packageIsCanonical = refl
  ; theoremBoundary =
      "P06 physical leaf: literal support, reduced-skeleton complexity linear in diameter, decoration multiplicity, canonical decomposition, and finite-range summation are sufficient for the existing P06 mixed reducer."
  }
  where
  open import Agda.Builtin.Equality using (refl)

p06PhysicalModelLeafAssemblyLevel : ProofLevel
p06PhysicalModelLeafAssemblyLevel = machineChecked

p06PhysicalSupportIdentificationLevel : ProofLevel
p06PhysicalSupportIdentificationLevel = conditional

p06ReducedSkeletonGeometryLevel : ProofLevel
p06ReducedSkeletonGeometryLevel = conditional

p06PhysicalDecorationAndDecompositionLevel : ProofLevel
p06PhysicalDecorationAndDecompositionLevel = conditional
