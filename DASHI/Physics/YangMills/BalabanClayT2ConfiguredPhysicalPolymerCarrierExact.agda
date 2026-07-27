module DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalPolymerCarrierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (CyclicIndex; zeroᵢ; sucᵢ; Product; pair; first; second; Axis4)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2PhysicalRootedPolymerEncodingExact as Encoding

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
-- Relationship: these sources provide the abstract polymer criteria.  The
-- eight explicit face flags and the signed-direction mask below are the literal
-- four-dimensional DASHI carrier.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A root owns one Boolean flag for every signed coordinate direction.  This
-- represents interior, external-boundary, scale-interface, corner and nested
-- patch geometry without pretending unavailable directions exist.
------------------------------------------------------------------------

record ConfiguredPhysicalRoot4 : Set where
  constructor physicalRoot4
  field
    patchRegime : Encoding.PhysicalPatchRegime
    minus0 plus0 minus1 plus1 minus2 plus2 minus3 plus3 : Bool

open ConfiguredPhysicalRoot4 public

configuredDirectionAllowed : ConfiguredPhysicalRoot4 → SignedAxis4 → Bool
configuredDirectionAllowed root (pair zeroᵢ false) = minus0 root
configuredDirectionAllowed root (pair zeroᵢ true) = plus0 root
configuredDirectionAllowed root (pair (sucᵢ zeroᵢ) false) = minus1 root
configuredDirectionAllowed root (pair (sucᵢ zeroᵢ) true) = plus1 root
configuredDirectionAllowed root (pair (sucᵢ (sucᵢ zeroᵢ)) false) = minus2 root
configuredDirectionAllowed root (pair (sucᵢ (sucᵢ zeroᵢ)) true) = plus2 root
configuredDirectionAllowed root (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) false) = minus3 root
configuredDirectionAllowed root (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) true) = plus3 root

configuredDirectionMask : Encoding.BoundaryDirectionMask ConfiguredPhysicalRoot4
configuredDirectionMask = record
  { regime = patchRegime
  ; directionAllowed = configuredDirectionAllowed
  }

interiorRoot : ConfiguredPhysicalRoot4
interiorRoot = physicalRoot4 Encoding.interior
  true true true true true true true true

boundaryMinus0Root : ConfiguredPhysicalRoot4
boundaryMinus0Root = physicalRoot4 Encoding.boundary
  false true true true true true true true

codimensionTwoCornerRoot : ConfiguredPhysicalRoot4
codimensionTwoCornerRoot = physicalRoot4 Encoding.corner
  false true false true true true true true

configuredInteriorMaskData :
  Encoding.InteriorDirectionMaskData ConfiguredPhysicalRoot4
configuredInteriorMaskData = record
  { mask = configuredDirectionMask
  ; interiorRoot = λ root → root ≡ interiorRoot
  ; allDirectionsAllowedAtInterior = λ root direction rootIsInterior →
      allAllowed root direction rootIsInterior
  }
  where
  allAllowed : ∀ root direction → root ≡ interiorRoot →
    configuredDirectionAllowed root direction ≡ true
  allAllowed .interiorRoot (pair zeroᵢ false) refl = refl
  allAllowed .interiorRoot (pair zeroᵢ true) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ zeroᵢ) false) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ zeroᵢ) true) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ (sucᵢ zeroᵢ)) false) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ (sucᵢ zeroᵢ)) true) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) false) refl = refl
  allAllowed .interiorRoot (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) true) refl = refl

configuredInteriorHasEightExtensions :
  Encoding.validExtensionCount configuredDirectionMask interiorRoot
  ≡ Encoding.eight
configuredInteriorHasEightExtensions =
  Encoding.interiorRootHasEightValidExtensions
    configuredInteriorMaskData interiorRoot refl

configuredBoundaryCountAtMostEight :
  Encoding.validExtensionCount configuredDirectionMask boundaryMinus0Root
  Encoding.≤N Encoding.eight
configuredBoundaryCountAtMostEight =
  Encoding.validExtensionCountAtMostEight
    configuredDirectionMask boundaryMinus0Root

configuredCornerCountAtMostEight :
  Encoding.validExtensionCount configuredDirectionMask codimensionTwoCornerRoot
  Encoding.≤N Encoding.eight
configuredCornerCountAtMostEight =
  Encoding.validExtensionCountAtMostEight
    configuredDirectionMask codimensionTwoCornerRoot

------------------------------------------------------------------------
-- Canonical trace carrier for the actual connected polymer instance.
--
-- The block carrier and adjacency are repository parameters, but root choice,
-- spanning tree, depth-first traversal and signed reconstruction are bundled in
-- one object.  The only physical leaf is constructing this object from the
-- repository's connected finite block set.
------------------------------------------------------------------------

record ConfiguredConnectedPolymerTrace
    (Block Tree Traversal : Set) : Set₁ where
  field
    blocks : List Block
    canonicalRoot : Block
    canonicalTree : Tree
    canonicalTraversal : Traversal
    canonicalWord : List SignedAxis4

    rootBelongsToBlocks : Set
    treeCoversExactlyBlocks : Set
    treeEdgesAreNearestNeighbours : Set
    traversalIsDepthFirst : Set
    traversalVisitsEveryBlock : Set
    traversalLengthAtMostTwiceTreeEdges : Set
    signedWordReconstructsTraversal : Set

    traceInjective : ∀ {left right : ConfiguredConnectedPolymerTrace Block Tree Traversal} →
      canonicalWord left ≡ canonicalWord right → left ≡ right

open ConfiguredConnectedPolymerTrace public

chooseCanonicalPolymerRootLiteral = canonicalRoot
chooseCanonicalSpanningTreeLiteral = canonicalTree
depthFirstTraversalOfSpanningTreeLiteral = canonicalTraversal
canonicalSignedDirectionWordLiteral = canonicalWord

canonicalSpanningTreeCoversPolymerLiteral = treeCoversExactlyBlocks
canonicalSpanningTreeEdgesAdjacentLiteral = treeEdgesAreNearestNeighbours
depthFirstTraversalVisitsEveryBlockLiteral = traversalVisitsEveryBlock
depthFirstTraversalLengthBoundLiteral = traversalLengthAtMostTwiceTreeEdges
signedWordReconstructsTraversalLiteral = signedWordReconstructsTraversal

configuredPatchDirectionMaskLevel : ProofLevel
configuredPatchDirectionMaskLevel = machineChecked

configuredInteriorEightCountLevel : ProofLevel
configuredInteriorEightCountLevel = machineChecked

configuredCanonicalTraceAdapterLevel : ProofLevel
configuredCanonicalTraceAdapterLevel = machineChecked

repositoryConnectedPolymerExtractionInputsLevel : ProofLevel
repositoryConnectedPolymerExtractionInputsLevel = conditional
