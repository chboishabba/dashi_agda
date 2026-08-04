module DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafLightweightExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel,
-- "Graph Theory", Graduate Texts in Mathematics 173, fifth edition,
-- Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
-- State the physical P06 model leaf using only finite graph, list and natural
-- number interfaces.  The legacy BalabanPolymerDiameterEntropy module imports a
-- much wider proof surface; on the present repository graph that reaches the
-- generated cyclotomic DFT regression.  None of that algebra is required to
-- state or check support, reduced-skeleton, decoration, and bounded-fibre
-- theorems.  This module is therefore the independently type-checkable P06
-- frontier.  A separate bridge may connect an inhabitant to legacy consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _^_; _≤_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanP06FiniteNeighbourGraphExact as FiniteGraph
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PhysicalPolymerSupportModel : Set₁ where
  field
    graph : FiniteGraph.FiniteNeighbourGraph
    Polymer : Set

    support : Polymer → List (FiniteGraph.Vertex graph)
    root : Polymer → FiniteGraph.Vertex graph

    Member :
      FiniteGraph.Vertex graph →
      List (FiniteGraph.Vertex graph) → Set
    NoDuplicates : List (FiniteGraph.Vertex graph) → Set
    Connected : List (FiniteGraph.Vertex graph) → Set
    PhysicalAdjacent :
      FiniteGraph.Vertex graph →
      FiniteGraph.Vertex graph → Set

    rootBelongsToSupport :
      ∀ polymer → Member (root polymer) (support polymer)

    supportHasNoDuplicates :
      ∀ polymer → NoDuplicates (support polymer)

    supportIsConnected :
      ∀ polymer → Connected (support polymer)

    supportAdjacencyForward :
      ∀ {left right} →
      FiniteGraph.Adjacent graph left right →
      PhysicalAdjacent left right

    supportAdjacencyBackward :
      ∀ {left right} →
      PhysicalAdjacent left right →
      FiniteGraph.Adjacent graph left right

    concreteDegreeBound : Nat
    concreteDegreeUniform :
      FiniteGraph.ConcreteBoundedDegree graph concreteDegreeBound

open PhysicalPolymerSupportModel public

record ReducedSkeletonGeometry
    (physical : PhysicalPolymerSupportModel) : Set₁ where
  field
    ReducedSkeleton : Set

    reducedSkeleton :
      Polymer physical → ReducedSkeleton

    reducedVertices :
      ReducedSkeleton → List (FiniteGraph.Vertex (graph physical))

    reducedComplexity : ReducedSkeleton → Nat
    supportDiameter : Polymer physical → Nat

    branchVertexCount segmentCount :
      ReducedSkeleton → Nat

    BranchVerticesSeparated : ReducedSkeleton → Set
    ReducedSegmentsInternallyDisjoint : ReducedSkeleton → Set
    EveryReducedSegmentHasPositiveLength : ReducedSkeleton → Set

    branchVerticesSeparated :
      ∀ skeleton → BranchVerticesSeparated skeleton

    reducedSegmentsInternallyDisjoint :
      ∀ skeleton → ReducedSegmentsInternallyDisjoint skeleton

    eachReducedSegmentPositiveLength :
      ∀ skeleton → EveryReducedSegmentHasPositiveLength skeleton

    segmentCountControlledByBranchCount :
      ∀ skeleton →
      segmentCount skeleton ≤
      branchVertexCount skeleton + branchVertexCount skeleton + 1

    branchCountCoefficient branchCountOffset : Nat

    branchCountControlledByDiameter :
      ∀ polymer →
      branchVertexCount (reducedSkeleton polymer)
      ≤ branchCountCoefficient * supportDiameter polymer
        + branchCountOffset

    complexityCoefficient complexityOffset : Nat

    reducedSkeletonComplexityLinearInDiameter :
      ∀ polymer →
      reducedComplexity (reducedSkeleton polymer)
      ≤ complexityCoefficient * supportDiameter polymer
        + complexityOffset

open ReducedSkeletonGeometry public

record PhysicalDecorationGeometry
    (physical : PhysicalPolymerSupportModel)
    (skeleton : ReducedSkeletonGeometry physical) : Set₁ where
  field
    Decoration DecorationCode : Set

    decoration : Polymer physical → Decoration
    encodeDecoration : Decoration → DecorationCode

    localChoiceBound : Nat
    decorationLength : Decoration → Nat

    LocalDecorationChoicesAtMost :
      FiniteGraph.Vertex (graph physical) → Nat → Set
    DecorationOwnedByReducedSkeleton : Polymer physical → Set

    localDecorationChoicesUniformlyBounded :
      ∀ block → LocalDecorationChoicesAtMost block localChoiceBound

    decorationSupportOwnedBySkeletonVertex :
      ∀ polymer → DecorationOwnedByReducedSkeleton polymer

    decorationEncodingInjective :
      ∀ {left right} →
      encodeDecoration left ≡ encodeDecoration right →
      left ≡ right

    decorationLengthCoefficient decorationLengthOffset : Nat

    decorationWordLengthLinearInReducedComplexity :
      ∀ polymer →
      decorationLength (decoration polymer)
      ≤ decorationLengthCoefficient
          * reducedComplexity skeleton
              (reducedSkeleton skeleton polymer)
        + decorationLengthOffset

    decorationCountAtComplexity : Nat → Nat
    decorationGrowthConstant : Nat

    decorationMultiplicityBound :
      ∀ complexity →
      decorationCountAtComplexity complexity
      ≤ decorationGrowthConstant ^ complexity

open PhysicalDecorationGeometry public

record PhysicalPolymerDecomposition
    (physical : PhysicalPolymerSupportModel)
    (skeleton : ReducedSkeletonGeometry physical)
    (decorations : PhysicalDecorationGeometry physical skeleton) : Set₁ where
  field
    Encoding : Set

    encode : Polymer physical → Encoding
    decode : Encoding → Polymer physical

    encodingCarriesReducedSkeleton :
      Encoding → ReducedSkeleton skeleton

    encodingCarriesDecoration :
      Encoding → Decoration decorations

    polymerHasCanonicalReducedSkeleton :
      ∀ polymer →
      encodingCarriesReducedSkeleton (encode polymer)
      ≡ reducedSkeleton skeleton polymer

    polymerHasCanonicalDecoration :
      ∀ polymer →
      encodingCarriesDecoration (encode polymer)
      ≡ decoration decorations polymer

    decodeEncodePolymer :
      ∀ polymer → decode (encode polymer) ≡ polymer

    fibreCardinality : Encoding → Nat
    fibreBound : Nat

    encodeFibreBound :
      ∀ code → fibreCardinality code ≤ fibreBound

open PhysicalPolymerDecomposition public

record P06LightweightPhysicalModelLeaf : Set₁ where
  field
    supportModel : PhysicalPolymerSupportModel
    reducedSkeletonModel : ReducedSkeletonGeometry supportModel
    decorationModel :
      PhysicalDecorationGeometry supportModel reducedSkeletonModel
    decompositionModel :
      PhysicalPolymerDecomposition
        supportModel reducedSkeletonModel decorationModel

    finiteRangeShellCount : Nat → Nat
    shellGrowthConstant : Nat

    finiteRangeExponentialSummation :
      ∀ diameter →
      finiteRangeShellCount diameter
      ≤ shellGrowthConstant ^ diameter

    theoremBoundary : String

open P06LightweightPhysicalModelLeaf public

canonicalSkeletonDecorationAnimalConstant :
  P06LightweightPhysicalModelLeaf → Nat
canonicalSkeletonDecorationAnimalConstant leaf =
  shellGrowthConstant leaf
  * decorationGrowthConstant (decorationModel leaf)
  * fibreBound (decompositionModel leaf)

record P06LightweightPhysicalReceipt
    (leaf : P06LightweightPhysicalModelLeaf) : Set₁ where
  field
    animalConstant : Nat
    animalConstantIsCanonical :
      animalConstant ≡ canonicalSkeletonDecorationAnimalConstant leaf

    rootedPolymerCountAtDiameter : Nat → Nat

    rootedPolymerDiameterBound :
      ∀ diameter →
      rootedPolymerCountAtDiameter diameter
      ≤ animalConstant ^ diameter

    receiptBoundary : String

open P06LightweightPhysicalReceipt public

p06LightweightInterfaceLevel : ProofLevel
p06LightweightInterfaceLevel = machineChecked

p06LiteralSupportInputsLevel : ProofLevel
p06LiteralSupportInputsLevel = conditional

p06ReducedSkeletonComplexityInputsLevel : ProofLevel
p06ReducedSkeletonComplexityInputsLevel = conditional

p06DecorationAndBoundedFibreInputsLevel : ProofLevel
p06DecorationAndBoundedFibreInputsLevel = conditional
