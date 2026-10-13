module DASHI.Reasoning.IITHyperfabricPartitionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.TypedHyperfabricCore as Hyperfabric
import DASHI.Reasoning.LocalFibreHyperfabricExact as Local
import DASHI.Topology.ClopenNDimFibreBoundary as NDim

------------------------------------------------------------------------
-- IIT / TYPED HYPERFABRIC PARTITION BRIDGE
--
-- Ordinary vertex partitions are not silently identified with cuts of the
-- repository's sheaf-like hyperfabric.  A hyperfabric cut must additionally
-- declare edge placement and carry a compatible global section plus receipts
-- for restriction/section semantics.
------------------------------------------------------------------------

record VertexOnlyCut (Vertex : Set) : Set where
  constructor vertexOnlyCut
  field
    vertexSide : Vertex → Bool
    vertexCutLabel : String

open VertexOnlyCut public

record HyperfabricCut
    {Vertex Edge : Set}
    (fabric : Hyperfabric.TypedHyperfabric Vertex Edge) : Set₁ where
  constructor hyperfabricCut
  field
    vertexSideH : Vertex → Bool
    edgeSideH : Edge → Bool
    compatibleSection : Hyperfabric.GlobalSection fabric
    restrictionCutReceipt : String
    sectionSeparationReceipt : String

open HyperfabricCut public

data PartitionSemantics : Set where
  graphVertexPartition : PartitionSemantics
  stalkRestrictionPartition : PartitionSemantics
  globalSectionPartition : PartitionSemantics

vertexPartitionNotDefinitionallySectionPartition :
  graphVertexPartition ≡ globalSectionPartition → ⊥
vertexPartitionNotDefinitionallySectionPartition ()

restrictionPartitionNotDefinitionallyGraphPartition :
  stalkRestrictionPartition ≡ graphVertexPartition → ⊥
restrictionPartitionNotDefinitionallyGraphPartition ()

oneDimensionalTriadicRefinement :
  NDim.immediateChildCount 1 ≡ 3
oneDimensionalTriadicRefinement = Local.oneDimTriadicChildren

twoDimensionalTriadicRefinement :
  NDim.immediateChildCount 2 ≡ 9
twoDimensionalTriadicRefinement = Local.twoDimTriadicChildren

threeDimensionalTriadicRefinement :
  NDim.immediateChildCount 3 ≡ 27
threeDimensionalTriadicRefinement = Local.threeDimTriadicChildren

record HyperfabricIITBoundary : Set where
  constructor hyperfabricIITBoundary
  field
    vertexCutsRepresentable : Bool
    edgeAndRestrictionCutsRepresentable : Bool
    compatibleGlobalSectionsAlreadyOwned : Bool
    graphSeparationEqualsSectionSeparationByDefinition : Bool
    localRefinementEqualsIntegrationIncreaseByDefinition : Bool
    braidTransportAutomaticallyPreservesIITPhi : Bool
    IITPartitionNeedsDeclaredHyperformalSemantics : Bool

open HyperfabricIITBoundary public

canonicalHyperfabricIITBoundary : HyperfabricIITBoundary
canonicalHyperfabricIITBoundary =
  hyperfabricIITBoundary
    true true true
    false false false true

graphAndSectionCutsRemainDistinct :
  graphSeparationEqualsSectionSeparationByDefinition
    canonicalHyperfabricIITBoundary ≡ false
graphAndSectionCutsRemainDistinct = refl

refinementDoesNotSelfPromoteToIntegration :
  localRefinementEqualsIntegrationIncreaseByDefinition
    canonicalHyperfabricIITBoundary ≡ false
refinementDoesNotSelfPromoteToIntegration = refl
