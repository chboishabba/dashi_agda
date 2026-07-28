module DASHI.Physics.YangMills.BalabanClayT2RepositoryConnectedPolymerExtractionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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

    polymerNonempty : ∀ polymer → Set
    polymerConnected : ∀ polymer → Set

    leastBlock : Polymer → Block
    leastBlockBelongs : ∀ polymer → Set
    leastBlockMinimal : ∀ polymer block → Set

    canonicalTree : Polymer → Tree
    treeCoversExactlyBlocks : ∀ polymer → Set
    treeEdgesAreNearestNeighbours : ∀ polymer → Set
    treeRootIsLeastBlock : ∀ polymer → Set
    leastParentTieBreakExact : ∀ polymer → Set

    depthFirstTraversal : Tree → Traversal
    traversalVisitsEveryTreeVertex : ∀ polymer → Set
    traversalUsesFixedSignedAxisOrder : ∀ polymer → Set
    traversalLengthAtMostTwiceTreeEdges : ∀ polymer → Set

    traversalWord : Traversal → List SignedAxis4
    signedWordReconstructsTraversal : ∀ polymer → Set

    -- Decoder includes the canonical root because a relative direction word by
    -- itself is translation invariant.
    decodePolymer : Block → List SignedAxis4 → Polymer
    decodeCanonicalTrace : ∀ polymer →
      decodePolymer (leastBlock polymer)
        (traversalWord (depthFirstTraversal (canonicalTree polymer)))
      ≡ polymer

    rootRecoverableFromPolymer : ∀ polymer →
      leastBlock
        (decodePolymer (leastBlock polymer)
          (traversalWord (depthFirstTraversal (canonicalTree polymer))))
      ≡ leastBlock polymer

open RepositoryConnectedBlockCarrier public

canonicalRoot = leastBlock
chooseCanonicalPolymerRootLiteral = leastBlock
chooseCanonicalSpanningTreeLiteral = canonicalTree
depthFirstTraversalOfSpanningTreeLiteral dataSet polymer =
  depthFirstTraversal dataSet (canonicalTree dataSet polymer)
canonicalSignedDirectionWordLiteral dataSet polymer =
  traversalWord dataSet
    (depthFirstTraversal dataSet (canonicalTree dataSet polymer))

canonicalRootBelongsToPolymer = leastBlockBelongs
canonicalSpanningTreeCoversPolymerLiteral = treeCoversExactlyBlocks
canonicalSpanningTreeEdgesAdjacentLiteral = treeEdgesAreNearestNeighbours
depthFirstTraversalVisitsEveryBlockLiteral = traversalVisitsEveryTreeVertex
depthFirstTraversalLengthBoundLiteral = traversalLengthAtMostTwiceTreeEdges
signedWordReconstructsTraversalLiteral = signedWordReconstructsTraversal

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
    (symmetry (decodeCanonicalTrace dataSet left))
    (trans
      (cong₂ (decodePolymer dataSet) rootEqual wordEqual)
      (decodeCanonicalTrace dataSet right))
  where
  open import Relation.Binary.PropositionalEquality using (sym)
  symmetry = sym
  cong₂ : ∀ {A B C : Set} {f : A → B → C} {a a' : A} {b b' : B} →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ refl refl = refl

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
