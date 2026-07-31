module DASHI.Physics.YangMills.BalabanClayT2RepositoryConnectedPolymerExtractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Sum using (_⊎_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)
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
-- Relationship: the papers require connected polymers and incompatibility but
-- do not provide this deterministic four-dimensional encoding.  DASHI uses a
-- least root, fixed signed-axis neighbour order, least-parent spanning tree,
-- fixed depth-first tour and a decoder.  Injectivity is derived from the decoder
-- left-inverse rather than assumed as a field.
------------------------------------------------------------------------

record RepositoryConnectedBlockCarrier
    (Polymer Block Tree Traversal : Set) : Set₁ where
  field
    blocksOf : Polymer → List Block

    blockLessEqual : Block → Block → Set
    blockOrderTotal : ∀ left right →
      blockLessEqual left right ⊎ blockLessEqual right left
    blockOrderAntisymmetric : ∀ {left right} →
      blockLessEqual left right → blockLessEqual right left → left ≡ right

    adjacent : Block → Block → Set
    signedStep : Block → SignedAxis4 → Block
    signedStepAdjacent : ∀ block direction → adjacent block (signedStep block direction)

    polymerNonempty : ∀ (polymer : Polymer) → Set
    polymerConnected : ∀ (polymer : Polymer) → Set

    leastBlock : Polymer → Block
    leastBlockBelongs : ∀ (polymer : Polymer) → Set
    leastBlockMinimal : ∀ (polymer : Polymer) (block : Block) → blockLessEqual (leastBlock polymer) block

    canonicalTree : Polymer → Tree
    treeCoversExactlyBlocks : ∀ (polymer : Polymer) → Set
    treeEdgesAreNearestNeighbours : ∀ (polymer : Polymer) → Set
    treeRootIsLeastBlock : ∀ (polymer : Polymer) → Set
    leastParentTieBreakExact : ∀ (polymer : Polymer) → Set

    depthFirstTraversal : Tree → Traversal
    traversalVisitsEveryTreeVertex : ∀ (polymer : Polymer) → Set
    traversalUsesFixedSignedAxisOrder : ∀ (polymer : Polymer) → Set
    traversalLengthAtMostTwiceTreeEdges : ∀ (polymer : Polymer) → Set

    traversalWord : Traversal → List SignedAxis4
    signedWordReconstructsTraversal : ∀ (polymer : Polymer) → Set

    -- Decoder includes the canonical root because a relative direction word by
    -- itself is translation invariant.
    decodePolymer : Block → List SignedAxis4 → Polymer
    decodeCanonicalTrace : ∀ (polymer : Polymer) →
      decodePolymer (leastBlock polymer)
        (traversalWord (depthFirstTraversal (canonicalTree polymer)))
      ≡ polymer

    rootRecoverableFromPolymer : ∀ (polymer : Polymer) →
      leastBlock
        (decodePolymer (leastBlock polymer)
          (traversalWord (depthFirstTraversal (canonicalTree polymer))))
      ≡ leastBlock polymer

open RepositoryConnectedBlockCarrier public

canonicalRoot : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Polymer → Block
canonicalRoot dataSet = leastBlock dataSet

chooseCanonicalPolymerRootLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Polymer → Block
chooseCanonicalPolymerRootLiteral dataSet = leastBlock dataSet

chooseCanonicalSpanningTreeLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Polymer → Tree
chooseCanonicalSpanningTreeLiteral dataSet = canonicalTree dataSet

depthFirstTraversalOfSpanningTreeLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Polymer → Traversal
depthFirstTraversalOfSpanningTreeLiteral dataSet polymer =
  depthFirstTraversal dataSet (canonicalTree dataSet polymer)

canonicalSignedDirectionWordLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Polymer → List SignedAxis4
canonicalSignedDirectionWordLiteral dataSet polymer =
  traversalWord dataSet
    (depthFirstTraversal dataSet (canonicalTree dataSet polymer))

canonicalRootBelongsToPolymer : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
canonicalRootBelongsToPolymer dataSet = leastBlockBelongs dataSet

canonicalSpanningTreeCoversPolymerLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
canonicalSpanningTreeCoversPolymerLiteral dataSet = treeCoversExactlyBlocks dataSet

canonicalSpanningTreeEdgesAdjacentLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
canonicalSpanningTreeEdgesAdjacentLiteral dataSet = treeEdgesAreNearestNeighbours dataSet

depthFirstTraversalVisitsEveryBlockLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
depthFirstTraversalVisitsEveryBlockLiteral dataSet = traversalVisitsEveryTreeVertex dataSet

depthFirstTraversalLengthBoundLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
depthFirstTraversalLengthBoundLiteral dataSet = traversalLengthAtMostTwiceTreeEdges dataSet

signedWordReconstructsTraversalLiteral : ∀ {Polymer Block Tree Traversal}
  (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  (polymer : Polymer) → Set
signedWordReconstructsTraversalLiteral dataSet = signedWordReconstructsTraversal dataSet

canonicalRootAndWordInjective :
  ∀ {Polymer Block Tree Traversal}
    (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal)
    {left right} →
  leastBlock dataSet left ≡ leastBlock dataSet right →
  canonicalSignedDirectionWordLiteral dataSet left
    ≡ canonicalSignedDirectionWordLiteral dataSet right →
  left ≡ right
canonicalRootAndWordInjective dataSet {left} {right} rootEqual wordEqual =
  trans
    (sym (decodeCanonicalTrace dataSet left))
    (trans
      (cong₂ (decodePolymer dataSet) rootEqual wordEqual)
      (decodeCanonicalTrace dataSet right))

record RootIncludedCanonicalCode
    (Polymer Block Tree Traversal Code : Set) : Set₁ where
  field
    carrier : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal
    encodeRootAndWord : Block → List SignedAxis4 → Code
    codeRootInjective : ∀ {rootLeft rootRight wordLeft wordRight} →
      encodeRootAndWord rootLeft wordLeft ≡ encodeRootAndWord rootRight wordRight →
      rootLeft ≡ rootRight
    codeWordInjective : ∀ {rootLeft rootRight wordLeft wordRight} →
      encodeRootAndWord rootLeft wordLeft ≡ encodeRootAndWord rootRight wordRight →
      wordLeft ≡ wordRight

open RootIncludedCanonicalCode public

canonicalCode :
  ∀ {Polymer Block Tree Traversal Code} →
  RootIncludedCanonicalCode Polymer Block Tree Traversal Code → Polymer → Code
canonicalCode dataSet polymer =
  encodeRootAndWord dataSet
    (leastBlock (carrier dataSet) polymer)
    (canonicalSignedDirectionWordLiteral (carrier dataSet) polymer)

canonicalCodeInjective :
  ∀ {Polymer Block Tree Traversal Code}
    (dataSet : RootIncludedCanonicalCode Polymer Block Tree Traversal Code)
    {left right} → canonicalCode dataSet left ≡ canonicalCode dataSet right →
  left ≡ right
canonicalCodeInjective dataSet codeEqual =
  canonicalRootAndWordInjective (carrier dataSet)
    (codeRootInjective dataSet codeEqual)
    (codeWordInjective dataSet codeEqual)

asConfiguredConnectedPolymerTraceFamily :
  ∀ {Polymer Block Tree Traversal}
    (dataSet : RepositoryConnectedBlockCarrier Polymer Block Tree Traversal) →
  Carrier.ConfiguredConnectedPolymerTraceFamily Polymer Block Tree Traversal
asConfiguredConnectedPolymerTraceFamily dataSet = record
  { traceOf = λ polymer → record
      { blocks = blocksOf dataSet polymer
      ; canonicalRoot = leastBlock dataSet polymer
      ; canonicalTree = canonicalTree dataSet polymer
      ; canonicalTraversal = depthFirstTraversal dataSet (canonicalTree dataSet polymer)
      ; canonicalWord = canonicalSignedDirectionWordLiteral dataSet polymer
      ; rootBelongsToBlocks = leastBlockBelongs dataSet polymer
      ; treeCoversExactlyBlocks = treeCoversExactlyBlocks dataSet polymer
      ; treeEdgesAreNearestNeighbours = treeEdgesAreNearestNeighbours dataSet polymer
      ; traversalIsDepthFirst = traversalUsesFixedSignedAxisOrder dataSet polymer
      ; traversalVisitsEveryBlock = traversalVisitsEveryTreeVertex dataSet polymer
      ; traversalLengthAtMostTwiceTreeEdges =
          traversalLengthAtMostTwiceTreeEdges dataSet polymer
      ; signedWordReconstructsTraversal =
          signedWordReconstructsTraversal dataSet polymer
      }
  ; traceInjective = λ {left} {right} wordEqual →
      canonicalRootAndWordInjective dataSet
        (blockOrderAntisymmetric dataSet
          (leastBlockMinimal dataSet left (leastBlock dataSet right))
          (leastBlockMinimal dataSet right (leastBlock dataSet left)))
        wordEqual
  }

canonicalRootTreeAlgorithmReductionLevel : ProofLevel
canonicalRootTreeAlgorithmReductionLevel = machineChecked

canonicalDecoderInjectivityLevel : ProofLevel
canonicalDecoderInjectivityLevel = machineChecked

configuredTraceFamilyAdapterLevel : ProofLevel
configuredTraceFamilyAdapterLevel = machineChecked

repositoryOrderConnectivityAndDecoderInputsLevel : ProofLevel
repositoryOrderConnectivityAndDecoderInputsLevel = conditional
