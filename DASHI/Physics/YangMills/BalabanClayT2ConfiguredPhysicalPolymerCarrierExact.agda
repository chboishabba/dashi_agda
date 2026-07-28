module DASHI.Physics.YangMills.BalabanClayT2ConfiguredPhysicalPolymerCarrierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (zeroᵢ; sucᵢ; pair)
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

configuredInteriorRoot : ConfiguredPhysicalRoot4
configuredInteriorRoot = physicalRoot4 Encoding.interior
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
  ; interiorRoot = λ root → root ≡ configuredInteriorRoot
  ; allDirectionsAllowedAtInterior = allAllowed
  }
  where
  allAllowed : ∀ root direction → root ≡ configuredInteriorRoot →
    configuredDirectionAllowed root direction ≡ true
  allAllowed .configuredInteriorRoot (pair zeroᵢ false) refl = refl
  allAllowed .configuredInteriorRoot (pair zeroᵢ true) refl = refl
  allAllowed .configuredInteriorRoot (pair (sucᵢ zeroᵢ) false) refl = refl
  allAllowed .configuredInteriorRoot (pair (sucᵢ zeroᵢ) true) refl = refl
  allAllowed .configuredInteriorRoot (pair (sucᵢ (sucᵢ zeroᵢ)) false) refl = refl
  allAllowed .configuredInteriorRoot (pair (sucᵢ (sucᵢ zeroᵢ)) true) refl = refl
  allAllowed .configuredInteriorRoot
    (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) false) refl = refl
  allAllowed .configuredInteriorRoot
    (pair (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) true) refl = refl

configuredInteriorHasEightExtensions :
  Encoding.validExtensionCount configuredDirectionMask configuredInteriorRoot
  ≡ Encoding.eight
configuredInteriorHasEightExtensions =
  Encoding.interiorRootHasEightValidExtensions
    configuredInteriorMaskData configuredInteriorRoot refl

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
-- Canonical trace carrier.  The trace data itself is non-recursive; injectivity
-- is a property of a family indexed by physical polymers.  This avoids placing
-- the record being defined in a negative field position.
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

open ConfiguredConnectedPolymerTrace public

record ConfiguredConnectedPolymerTraceFamily
    (Polymer Block Tree Traversal : Set) : Set₁ where
  field
    traceOf : Polymer → ConfiguredConnectedPolymerTrace Block Tree Traversal
    traceInjective : ∀ {left right} →
      canonicalWord (traceOf left) ≡ canonicalWord (traceOf right) →
      left ≡ right

open ConfiguredConnectedPolymerTraceFamily public

chooseCanonicalPolymerRootLiteral family polymer =
  canonicalRoot (traceOf family polymer)
chooseCanonicalSpanningTreeLiteral family polymer =
  canonicalTree (traceOf family polymer)
depthFirstTraversalOfSpanningTreeLiteral family polymer =
  canonicalTraversal (traceOf family polymer)
canonicalSignedDirectionWordLiteral family polymer =
  canonicalWord (traceOf family polymer)

canonicalSpanningTreeCoversPolymerLiteral family polymer =
  treeCoversExactlyBlocks (traceOf family polymer)
canonicalSpanningTreeEdgesAdjacentLiteral family polymer =
  treeEdgesAreNearestNeighbours (traceOf family polymer)
depthFirstTraversalVisitsEveryBlockLiteral family polymer =
  traversalVisitsEveryBlock (traceOf family polymer)
depthFirstTraversalLengthBoundLiteral family polymer =
  traversalLengthAtMostTwiceTreeEdges (traceOf family polymer)
signedWordReconstructsTraversalLiteral family polymer =
  signedWordReconstructsTraversal (traceOf family polymer)
canonicalPhysicalTraceInjectiveLiteral = traceInjective

configuredPatchDirectionMaskLevel : ProofLevel
configuredPatchDirectionMaskLevel = machineChecked

configuredInteriorEightCountLevel : ProofLevel
configuredInteriorEightCountLevel = machineChecked

configuredCanonicalTraceAdapterLevel : ProofLevel
configuredCanonicalTraceAdapterLevel = machineChecked

repositoryConnectedPolymerExtractionInputsLevel : ProofLevel
repositoryConnectedPolymerExtractionInputsLevel = conditional
