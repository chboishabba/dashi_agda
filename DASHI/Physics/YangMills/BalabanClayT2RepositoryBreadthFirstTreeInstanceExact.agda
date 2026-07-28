module DASHI.Physics.YangMills.BalabanClayT2RepositoryBreadthFirstTreeInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2RepositoryConnectedPolymerExtractionExact as Extraction

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
    physicalBlockOrderTotal : ∀ left right →
      blockLessEqual left right ⊎ blockLessEqual right left
    physicalBlockOrderAntisymmetric : ∀ {left right} →
      blockLessEqual left right → blockLessEqual right left → left ≡ right
    physicalBlockOrderDecidable : ∀ left right → Set

    physicalNearestNeighbour : Block → Block → Set
    physicalNearestNeighbourDecidable : ∀ left right → Set
    signedStep : Block → SignedAxis4 → Block
    directionOfAdjacentBlocks : Block → Block → SignedAxis4
    signedStepAdjacent : ∀ block direction →
      physicalNearestNeighbour block (signedStep block direction)
    decodeDirectionStepExact : ∀ left right →
      physicalNearestNeighbour left right →
      signedStep left (directionOfAdjacentBlocks left right) ≡ right

    connectedPolymerNonempty : ∀ polymer → Set
    connectedPolymerPathExists : ∀ polymer left right → Set

    leastBlockOfNonemptyPolymer : Polymer → Block
    leastBlockBelongsToPolymer : ∀ polymer → Set
    leastBlockMinimal : ∀ polymer block → Set

    breadthFirstDistance : Polymer → Block → Nat
    rootDistanceZero : ∀ polymer → Set
    everyNonRootHasCloserNeighbour : ∀ polymer block → Set

    canonicalParentOfNonRootBlock : Polymer → Block → Block
    canonicalParentBelongsToPolymer : ∀ polymer block → Set
    canonicalParentIsNeighbour : ∀ polymer block → Set
    canonicalParentStrictlyCloserToRoot : ∀ polymer block → Set
    canonicalParentIsLeastCloserNeighbour : ∀ polymer block → Set

    canonicalTree : Polymer → Tree
    canonicalTreeEdgesAreParentEdges : ∀ polymer → Set
    canonicalSpanningTreeAcyclic : ∀ polymer → Set
    canonicalSpanningTreeConnected : ∀ polymer → Set
    canonicalSpanningTreeCoversExactlyPolymer : ∀ polymer → Set
    canonicalTreeRootIsLeastBlock : ∀ polymer → Set

    canonicalDepthFirstTour : Tree → Traversal
    depthFirstTourUsesFixedAxisOrder : ∀ polymer → Set
    depthFirstTourVisitsEveryTreeVertex : ∀ polymer → Set
    depthFirstTourLengthEqualsTwiceEdges : ∀ polymer → Set

    traversalWord : Traversal → List SignedAxis4
    signedWordReconstructsTraversal : ∀ polymer → Set

    canonicalWordDecoder : Block → List SignedAxis4 → Polymer
    decoderReplaysBacktrackingExactly : ∀ polymer → Set
    decoderOfCanonicalWordExact : ∀ polymer →
      canonicalWordDecoder (leastBlockOfNonemptyPolymer polymer)
        (traversalWord (canonicalDepthFirstTour (canonicalTree polymer)))
      ≡ polymer

    rootRecoverableAfterDecode : ∀ polymer →
      leastBlockOfNonemptyPolymer
        (canonicalWordDecoder (leastBlockOfNonemptyPolymer polymer)
          (traversalWord (canonicalDepthFirstTour (canonicalTree polymer))))
      ≡ leastBlockOfNonemptyPolymer polymer

open RepositoryBreadthFirstTreeData public

physicalBlockLexicographicOrder = blockLessEqual
leastBlock = leastBlockOfNonemptyPolymer
canonicalParent = canonicalParentOfNonRootBlock
canonicalSpanningTree = canonicalTree
canonicalDepthFirstTraversal dataSet polymer =
  canonicalDepthFirstTour dataSet (canonicalTree dataSet polymer)
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
  ; polymerConnected = λ polymer → connectedPolymerPathExists dataSet polymer
  ; leastBlock = leastBlockOfNonemptyPolymer dataSet
  ; leastBlockBelongs = leastBlockBelongsToPolymer dataSet
  ; leastBlockMinimal = leastBlockMinimal dataSet
  ; canonicalTree = canonicalTree dataSet
  ; treeCoversExactlyBlocks = canonicalSpanningTreeCoversExactlyPolymer dataSet
  ; treeEdgesAreNearestNeighbours = λ polymer →
      canonicalTreeEdgesAreParentEdges dataSet polymer ,
      canonicalParentIsNeighbour dataSet polymer
  ; treeRootIsLeastBlock = canonicalTreeRootIsLeastBlock dataSet
  ; leastParentTieBreakExact = λ polymer →
      canonicalParentIsLeastCloserNeighbour dataSet polymer
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
