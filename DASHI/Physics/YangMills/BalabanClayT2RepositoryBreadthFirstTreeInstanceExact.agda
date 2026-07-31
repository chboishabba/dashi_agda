module DASHI.Physics.YangMills.BalabanClayT2RepositoryBreadthFirstTreeInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum using (_⊎_)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2RepositoryConnectedPolymerExtractionExact as Extraction
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalPolymerCarrierExact as Carrier

------------------------------------------------------------------------
-- Literature normalization.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- Roberto Fernández and Aldo Procacci, "Cluster Expansion for Abstract Polymer
-- Models. New Bounds from an Old Approach", Communications in Mathematical
-- Physics 274 (2007), 123--140. DOI: 10.1007/s00220-007-0279-2
--
-- Relationship: connected polymers are required by the cluster criteria.  The
-- breadth-first distance, least parent, deterministic DFS and decoder below are
-- DASHI's finite four-dimensional canonical encoding.
------------------------------------------------------------------------

record RepositoryBreadthFirstTreeData
    (Polymer Block Tree Traversal : Set) : Set₁ where
  field
    blocksOf : Polymer → List Block

    blockLessEqual : Block → Block → Set
    physicalBlockOrderTotal : ∀ (left right : Block) →
      blockLessEqual left right ⊎ blockLessEqual right left
    physicalBlockOrderAntisymmetric : ∀ {left right : Block} →
      blockLessEqual left right → blockLessEqual right left → left ≡ right
    physicalBlockOrderDecidable : ∀ (left right : Block) → Set

    physicalNearestNeighbour : Block → Block → Set
    physicalNearestNeighbourDecidable : ∀ (left right : Block) → Set
    signedStep : Block → SignedAxis4 → Block
    directionOfAdjacentBlocks : Block → Block → SignedAxis4
    signedStepAdjacent : ∀ (block : Block) (direction : SignedAxis4) →
      physicalNearestNeighbour block (signedStep block direction)
    decodeDirectionStepExact : ∀ (left right : Block) →
      physicalNearestNeighbour left right →
      signedStep left (directionOfAdjacentBlocks left right) ≡ right

    connectedPolymerNonempty : ∀ (polymer : Polymer) → Set
    connectedPolymerPathExists : ∀ (polymer : Polymer) (left right : Block) → Set

    leastBlockOfNonemptyPolymer : Polymer → Block
    leastBlockBelongsToPolymer : ∀ (polymer : Polymer) → Set
    leastBlockMinimal : ∀ (polymer : Polymer) (block : Block) → blockLessEqual (leastBlockOfNonemptyPolymer polymer) block

    breadthFirstDistance : Polymer → Block → Nat
    rootDistanceZero : ∀ (polymer : Polymer) → Set
    everyNonRootHasCloserNeighbour : ∀ (polymer : Polymer) (block : Block) → Set

    canonicalParentOfNonRootBlock : Polymer → Block → Block
    canonicalParentBelongsToPolymer : ∀ (polymer : Polymer) (block : Block) → Set
    canonicalParentIsNeighbour : ∀ (polymer : Polymer) (block : Block) → Set
    canonicalParentStrictlyCloserToRoot : ∀ (polymer : Polymer) (block : Block) → Set
    canonicalParentIsLeastCloserNeighbour : ∀ (polymer : Polymer) (block : Block) → Set

    canonicalTree : Polymer → Tree
    canonicalTreeEdgesAreParentEdges : ∀ (polymer : Polymer) → Set
    canonicalSpanningTreeAcyclic : ∀ (polymer : Polymer) → Set
    canonicalSpanningTreeConnected : ∀ (polymer : Polymer) → Set
    canonicalSpanningTreeCoversExactlyPolymer : ∀ (polymer : Polymer) → Set
    canonicalTreeRootIsLeastBlock : ∀ (polymer : Polymer) → Set

    canonicalDepthFirstTour : Tree → Traversal
    depthFirstTourUsesFixedAxisOrder : ∀ (polymer : Polymer) → Set
    depthFirstTourVisitsEveryTreeVertex : ∀ (polymer : Polymer) → Set
    depthFirstTourLengthEqualsTwiceEdges : ∀ (polymer : Polymer) → Set

    traversalWord : Traversal → List SignedAxis4
    signedWordReconstructsTraversal : ∀ (polymer : Polymer) → Set

    canonicalWordDecoder : Block → List SignedAxis4 → Polymer
    decoderReplaysBacktrackingExactly : ∀ (polymer : Polymer) → Set
    decoderOfCanonicalWordExact : ∀ (polymer : Polymer) →
      canonicalWordDecoder (leastBlockOfNonemptyPolymer polymer)
        (traversalWord (canonicalDepthFirstTour (canonicalTree polymer)))
      ≡ polymer

    rootRecoverableAfterDecode : ∀ (polymer : Polymer) →
      leastBlockOfNonemptyPolymer
        (canonicalWordDecoder (leastBlockOfNonemptyPolymer polymer)
          (traversalWord (canonicalDepthFirstTour (canonicalTree polymer))))
      ≡ leastBlockOfNonemptyPolymer polymer

open RepositoryBreadthFirstTreeData public

physicalBlockLexicographicOrder : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Block → Block → Set
physicalBlockLexicographicOrder dataSet = blockLessEqual dataSet

leastBlock : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Polymer → Block
leastBlock dataSet = leastBlockOfNonemptyPolymer dataSet

canonicalParent : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Polymer → Block → Block
canonicalParent dataSet = canonicalParentOfNonRootBlock dataSet

canonicalSpanningTree : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Polymer → Tree
canonicalSpanningTree dataSet = canonicalTree dataSet

canonicalDepthFirstTraversal : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Polymer → Traversal
canonicalDepthFirstTraversal dataSet polymer =
  canonicalDepthFirstTour dataSet (canonicalTree dataSet polymer)

canonicalDirectionWord : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Polymer → List SignedAxis4
canonicalDirectionWord dataSet polymer =
  traversalWord dataSet (canonicalDepthFirstTraversal dataSet polymer)

asRepositoryConnectedBlockCarrier :
  ∀ {Polymer Block Tree Traversal} →
  RepositoryBreadthFirstTreeData Polymer Block Tree Traversal →
  Extraction.RepositoryConnectedBlockCarrier Polymer Block Tree Traversal
asRepositoryConnectedBlockCarrier dataSet = record
  { blocksOf = blocksOf dataSet
  ; blockLessEqual = blockLessEqual dataSet
  ; blockOrderTotal = physicalBlockOrderTotal dataSet
  ; blockOrderAntisymmetric = physicalBlockOrderAntisymmetric dataSet
  ; adjacent = physicalNearestNeighbour dataSet
  ; signedStep = signedStep dataSet
  ; signedStepAdjacent = signedStepAdjacent dataSet
  ; polymerNonempty = connectedPolymerNonempty dataSet
  ; polymerConnected = λ polymer → ∀ left right → connectedPolymerPathExists dataSet polymer left right
  ; leastBlock = leastBlockOfNonemptyPolymer dataSet
  ; leastBlockBelongs = leastBlockBelongsToPolymer dataSet
  ; leastBlockMinimal = leastBlockMinimal dataSet
  ; canonicalTree = canonicalTree dataSet
  ; treeCoversExactlyBlocks = canonicalSpanningTreeCoversExactlyPolymer dataSet
  ; treeEdgesAreNearestNeighbours = λ polymer →
      canonicalTreeEdgesAreParentEdges dataSet polymer ×
      (∀ block → canonicalParentIsNeighbour dataSet polymer block)
  ; treeRootIsLeastBlock = canonicalTreeRootIsLeastBlock dataSet
  ; leastParentTieBreakExact = λ polymer →
      ∀ block → canonicalParentIsLeastCloserNeighbour dataSet polymer block
  ; depthFirstTraversal = canonicalDepthFirstTour dataSet
  ; traversalVisitsEveryTreeVertex = depthFirstTourVisitsEveryTreeVertex dataSet
  ; traversalUsesFixedSignedAxisOrder = depthFirstTourUsesFixedAxisOrder dataSet
  ; traversalLengthAtMostTwiceTreeEdges = λ polymer →
      depthFirstTourLengthEqualsTwiceEdges dataSet polymer
  ; traversalWord = traversalWord dataSet
  ; signedWordReconstructsTraversal = signedWordReconstructsTraversal dataSet
  ; decodePolymer = canonicalWordDecoder dataSet
  ; decodeCanonicalTrace = decoderOfCanonicalWordExact dataSet
  ; rootRecoverableFromPolymer = rootRecoverableAfterDecode dataSet
  }
  where open import Data.Product using (_,_)

canonicalTraceInjective :
  ∀ {Polymer Block Tree Traversal}
    (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal)
    {left right} →
  leastBlock dataSet left ≡ leastBlock dataSet right →
  canonicalDirectionWord dataSet left ≡ canonicalDirectionWord dataSet right →
  left ≡ right
canonicalTraceInjective dataSet =
  Extraction.canonicalRootAndWordInjective
    (asRepositoryConnectedBlockCarrier dataSet)

asConfiguredConnectedPolymerTraceFamily :
  ∀ {Polymer Block Tree Traversal} →
  (dataSet : RepositoryBreadthFirstTreeData Polymer Block Tree Traversal) →
  Carrier.ConfiguredConnectedPolymerTraceFamily Polymer Block Tree Traversal
asConfiguredConnectedPolymerTraceFamily dataSet =
  Extraction.asConfiguredConnectedPolymerTraceFamily
    (asRepositoryConnectedBlockCarrier dataSet)

breadthFirstParentReductionLevel : ProofLevel
breadthFirstParentReductionLevel = machineChecked

deterministicDepthFirstReductionLevel : ProofLevel
deterministicDepthFirstReductionLevel = machineChecked

decoderLeftInverseReductionLevel : ProofLevel
decoderLeftInverseReductionLevel = machineChecked

repositoryBreadthFirstOrderConnectivityInputsLevel : ProofLevel
repositoryBreadthFirstOrderConnectivityInputsLevel = conditional
