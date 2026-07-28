module DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤ᵇ_)
open import Data.Sum using (_⊎_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2RepositoryBreadthFirstTreeInstanceExact as BFS

------------------------------------------------------------------------
-- Actual periodic block and finite-polymer carrier for the BFS trace lane.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci, "Cluster Expansion for Abstract Polymer
-- Models. New Bounds from an Old Approach", Communications in Mathematical
-- Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2.
--
-- Relationship: the papers consume connected polymers.  The concrete finite
-- torus block/list/tree/traversal representation below is DASHI-specific.
------------------------------------------------------------------------

PeriodicBlock : Nat → Set
PeriodicBlock n = periodicTorus4Definition (suc n)

PeriodicPolymer : Nat → Set
PeriodicPolymer n = List (PeriodicBlock n)

cyclicRank : ∀ {n} → CyclicIndex n → Nat
cyclicRank zeroᵢ = zero
cyclicRank (sucᵢ index) = suc (cyclicRank index)

blockCoordinate0 : ∀ {n} → PeriodicBlock n → CyclicIndex (suc n)
blockCoordinate0 block = first (first block)

blockCoordinate1 : ∀ {n} → PeriodicBlock n → CyclicIndex (suc n)
blockCoordinate1 block = second (first block)

blockCoordinate2 : ∀ {n} → PeriodicBlock n → CyclicIndex (suc n)
blockCoordinate2 block = first (second block)

blockCoordinate3 : ∀ {n} → PeriodicBlock n → CyclicIndex (suc n)
blockCoordinate3 block = second (second block)

natEqualBool : Nat → Nat → Bool
natEqualBool zero zero = true
natEqualBool zero (suc _) = false
natEqualBool (suc _) zero = false
natEqualBool (suc left) (suc right) = natEqualBool left right

lexLe4Bool : ∀ {n} → PeriodicBlock n → PeriodicBlock n → Bool
lexLe4Bool left right with
  natEqualBool (cyclicRank (blockCoordinate0 left))
    (cyclicRank (blockCoordinate0 right))
... | false = cyclicRank (blockCoordinate0 left) ≤ᵇ cyclicRank (blockCoordinate0 right)
... | true with
  natEqualBool (cyclicRank (blockCoordinate1 left))
    (cyclicRank (blockCoordinate1 right))
... | false = cyclicRank (blockCoordinate1 left) ≤ᵇ cyclicRank (blockCoordinate1 right)
... | true with
  natEqualBool (cyclicRank (blockCoordinate2 left))
    (cyclicRank (blockCoordinate2 right))
... | false = cyclicRank (blockCoordinate2 left) ≤ᵇ cyclicRank (blockCoordinate2 right)
... | true = cyclicRank (blockCoordinate3 left) ≤ᵇ cyclicRank (blockCoordinate3 right)

blockLessEqual : ∀ {n} → PeriodicBlock n → PeriodicBlock n → Set
blockLessEqual left right = lexLe4Bool left right ≡ true

zeroBlock : ∀ {n} → PeriodicBlock n
zeroBlock = pair (pair zeroᵢ zeroᵢ) (pair zeroᵢ zeroᵢ)

chooseLeast : ∀ {n} → PeriodicBlock n → PeriodicBlock n → PeriodicBlock n
chooseLeast left right with lexLe4Bool left right
... | true = left
... | false = right

leastBlockList : ∀ {n} → List (PeriodicBlock n) → PeriodicBlock n
leastBlockList [] = zeroBlock
leastBlockList (block ∷ blocks) = chooseLeast block (leastBlockList blocks)

record ParentEdge (n : Nat) : Set where
  constructor parentEdge
  field
    child parent : PeriodicBlock n

open ParentEdge public

PeriodicTree : Nat → Set
PeriodicTree n = List (ParentEdge n)

PeriodicTraversal : Nat → Set
PeriodicTraversal n = List (PeriodicBlock n)

record PeriodicPolymerEvidence (n : Nat) (polymer : PeriodicPolymer n) : Set₁ where
  field
    nonempty : Set
    duplicateFree : Set
    connectedByNearestNeighbourPaths : Set
    leastBlockBelongs : Set
    leastBlockMinimal : ∀ block → Set

open PeriodicPolymerEvidence public

record PeriodicAdjacencyData (n : Nat) : Set₁ where
  field
    nearestNeighbour : PeriodicBlock n → PeriodicBlock n → Set
    nearestNeighbourDecidable : ∀ left right → Set
    signedStep : PeriodicBlock n → SignedAxis4 → PeriodicBlock n
    directionOfAdjacent : PeriodicBlock n → PeriodicBlock n → SignedAxis4
    signedStepAdjacent : ∀ block direction →
      nearestNeighbour block (signedStep block direction)
    directionReconstructsAdjacent : ∀ left right →
      nearestNeighbour left right →
      signedStep left (directionOfAdjacent left right) ≡ right

open PeriodicAdjacencyData public

record PeriodicBreadthFirstImplementation (n : Nat) : Set₁ where
  field
    adjacency : PeriodicAdjacencyData n
    evidence : ∀ polymer → PeriodicPolymerEvidence n polymer

    blockOrderTotal : ∀ left right →
      blockLessEqual left right ⊎ blockLessEqual right left
    blockOrderAntisymmetric : ∀ {left right} →
      blockLessEqual left right → blockLessEqual right left → left ≡ right
    blockOrderDecidable : ∀ left right → Set

    breadthFirstDistance : PeriodicPolymer n → PeriodicBlock n → Nat
    rootDistanceZero : ∀ polymer → Set
    everyNonRootHasCloserNeighbour : ∀ polymer block → Set

    canonicalParent : PeriodicPolymer n → PeriodicBlock n → PeriodicBlock n
    canonicalParentBelongs : ∀ polymer block → Set
    canonicalParentAdjacent : ∀ polymer block → Set
    canonicalParentDistanceDecreases : ∀ polymer block → Set
    canonicalParentLeastAmongCloser : ∀ polymer block → Set

    parentTree : PeriodicPolymer n → PeriodicTree n
    parentTreeEdgesExact : ∀ polymer → Set
    parentTreeAcyclic : ∀ polymer → Set
    parentTreeConnected : ∀ polymer → Set
    parentTreeCoversExactly : ∀ polymer → Set
    parentTreeRootExact : ∀ polymer → Set

    depthFirstTour : PeriodicTree n → PeriodicTraversal n
    depthFirstUsesSignedAxisOrder : ∀ polymer → Set
    depthFirstVisitsEveryBlock : ∀ polymer → Set
    depthFirstLengthTwiceEdges : ∀ polymer → Set

    traversalWord : PeriodicTraversal n → List SignedAxis4
    signedWordReconstructsTraversal : ∀ polymer → Set

    decodePolymer : PeriodicBlock n → List SignedAxis4 → PeriodicPolymer n
    decoderReplaysBacktracking : ∀ polymer → Set
    decodeCanonicalTrace : ∀ polymer →
      decodePolymer (leastBlockList polymer)
        (traversalWord (depthFirstTour (parentTree polymer)))
      ≡ polymer
    rootRecoverableAfterDecode : ∀ polymer →
      leastBlockList
        (decodePolymer (leastBlockList polymer)
          (traversalWord (depthFirstTour (parentTree polymer))))
      ≡ leastBlockList polymer

open PeriodicBreadthFirstImplementation public

asRepositoryBreadthFirstTreeData :
  ∀ {n} → PeriodicBreadthFirstImplementation n →
  BFS.RepositoryBreadthFirstTreeData
    (PeriodicPolymer n) (PeriodicBlock n) (PeriodicTree n) (PeriodicTraversal n)
asRepositoryBreadthFirstTreeData dataSet = record
  { blocksOf = λ polymer → polymer
  ; blockLessEqual = blockLessEqual
  ; physicalBlockOrderTotal = blockOrderTotal dataSet
  ; physicalBlockOrderAntisymmetric = blockOrderAntisymmetric dataSet
  ; physicalBlockOrderDecidable = blockOrderDecidable dataSet
  ; physicalNearestNeighbour = nearestNeighbour (adjacency dataSet)
  ; physicalNearestNeighbourDecidable = nearestNeighbourDecidable (adjacency dataSet)
  ; signedStep = signedStep (adjacency dataSet)
  ; directionOfAdjacentBlocks = directionOfAdjacent (adjacency dataSet)
  ; signedStepAdjacent = signedStepAdjacent (adjacency dataSet)
  ; decodeDirectionStepExact = directionReconstructsAdjacent (adjacency dataSet)
  ; connectedPolymerNonempty = λ polymer → nonempty (evidence dataSet polymer)
  ; connectedPolymerPathExists = λ polymer _ _ →
      connectedByNearestNeighbourPaths (evidence dataSet polymer)
  ; leastBlockOfNonemptyPolymer = leastBlockList
  ; leastBlockBelongsToPolymer = λ polymer → leastBlockBelongs (evidence dataSet polymer)
  ; leastBlockMinimal = λ polymer → leastBlockMinimal (evidence dataSet polymer)
  ; breadthFirstDistance = breadthFirstDistance dataSet
  ; rootDistanceZero = rootDistanceZero dataSet
  ; everyNonRootHasCloserNeighbour = everyNonRootHasCloserNeighbour dataSet
  ; canonicalParentOfNonRootBlock = canonicalParent dataSet
  ; canonicalParentBelongsToPolymer = canonicalParentBelongs dataSet
  ; canonicalParentIsNeighbour = canonicalParentAdjacent dataSet
  ; canonicalParentStrictlyCloserToRoot = canonicalParentDistanceDecreases dataSet
  ; canonicalParentIsLeastCloserNeighbour = canonicalParentLeastAmongCloser dataSet
  ; canonicalTree = parentTree dataSet
  ; canonicalTreeEdgesAreParentEdges = parentTreeEdgesExact dataSet
  ; canonicalSpanningTreeAcyclic = parentTreeAcyclic dataSet
  ; canonicalSpanningTreeConnected = parentTreeConnected dataSet
  ; canonicalSpanningTreeCoversExactlyPolymer = parentTreeCoversExactly dataSet
  ; canonicalTreeRootIsLeastBlock = parentTreeRootExact dataSet
  ; canonicalDepthFirstTour = depthFirstTour dataSet
  ; depthFirstTourUsesFixedAxisOrder = depthFirstUsesSignedAxisOrder dataSet
  ; depthFirstTourVisitsEveryTreeVertex = depthFirstVisitsEveryBlock dataSet
  ; depthFirstTourLengthEqualsTwiceEdges = depthFirstLengthTwiceEdges dataSet
  ; traversalWord = traversalWord dataSet
  ; signedWordReconstructsTraversal = signedWordReconstructsTraversal dataSet
  ; canonicalWordDecoder = decodePolymer dataSet
  ; decoderReplaysBacktrackingExactly = decoderReplaysBacktracking dataSet
  ; decoderOfCanonicalWordExact = decodeCanonicalTrace dataSet
  ; rootRecoverableAfterDecode = rootRecoverableAfterDecode dataSet
  }

periodicBlockCarrierLevel : ProofLevel
periodicBlockCarrierLevel = machineChecked

periodicLexicographicDefinitionLevel : ProofLevel
periodicLexicographicDefinitionLevel = machineChecked

periodicBFSAdapterLevel : ProofLevel
periodicBFSAdapterLevel = machineChecked

periodicAdjacencyAndBFSEvidenceInputsLevel : ProofLevel
periodicAdjacencyAndBFSEvidenceInputsLevel = conditional
