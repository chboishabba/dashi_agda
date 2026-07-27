module DASHI.Physics.YangMills.BalabanClayT2PhysicalPolymerCarrierInstanceExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
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
-- Relationship: the papers provide the abstract incompatibility criterion.  The
-- canonical root/tree/traversal and patch-direction masks below are DASHI's
-- physical lattice instance and are not supplied by abstract polymer theory.
------------------------------------------------------------------------

record LiteralPhysicalPolymerCarrierInstance
    (Polymer Block Root Tree Traversal : Set) : Set₁ where
  field
    traceData : Encoding.CanonicalPhysicalPolymerTraceData Polymer Block
    cliqueData : Encoding.PhysicalRootedExtensionClique Polymer Block Root

    treeOf : Polymer → Tree
    traversalOf : Tree → Traversal

    canonicalRootBelongsToPolymer : ∀ polymer → Set
    canonicalSpanningTreeCoversPolymer : ∀ polymer → Set
    canonicalSpanningTreeEdgesAdjacent : ∀ polymer → Set
    depthFirstTraversalVisitsEveryBlock : ∀ polymer → Set
    depthFirstTraversalLengthBound : ∀ polymer → Set
    signedWordReconstructsTraversal : ∀ polymer → Set

    -- The actual patch masks, not merely the abstract at-most-eight theorem.
    boundaryDirectionMaskCorrect : ∀ root →
      Encoding.regime (Encoding.directionMask cliqueData) root
      ≡ Encoding.boundary → Set

    interfaceDirectionMaskCorrect : ∀ root →
      Encoding.regime (Encoding.directionMask cliqueData) root
      ≡ Encoding.scaleInterface → Set

    cornerDirectionMaskCorrect : ∀ root →
      Encoding.regime (Encoding.directionMask cliqueData) root
      ≡ Encoding.corner → Set

    nestedDirectionMaskCorrect : ∀ root →
      Encoding.regime (Encoding.directionMask cliqueData) root
      ≡ Encoding.nested → Set

    validPhysicalExtensionsShareParentCore : ∀ root first second →
      Encoding.literalValidExtension
        (Encoding.directionMask cliqueData) root first →
      Encoding.literalValidExtension
        (Encoding.directionMask cliqueData) root second →
      Set

    sharedParentCoreImpliesPhysicalIncompatibility : ∀ root first second →
      Set

open LiteralPhysicalPolymerCarrierInstance public

canonicalPhysicalTraceInjectiveLiteral :
  ∀ {Polymer Block Root Tree Traversal}
    (dataSet : LiteralPhysicalPolymerCarrierInstance
      Polymer Block Root Tree Traversal)
    {left right} →
  Encoding.canonicalSignedDirectionWord (traceData dataSet) left
  ≡ Encoding.canonicalSignedDirectionWord (traceData dataSet) right →
  left ≡ right
canonicalPhysicalTraceInjectiveLiteral dataSet =
  Encoding.physicalPolymerCanonicalTraceInjective (traceData dataSet)

boundaryExtensionCountAtMostEightLiteral :
  ∀ {Polymer Block Root Tree Traversal}
    (dataSet : LiteralPhysicalPolymerCarrierInstance
      Polymer Block Root Tree Traversal)
    root →
  Encoding.regime (Encoding.directionMask (cliqueData dataSet)) root
  ≡ Encoding.boundary →
  Encoding._≤N_
    (Encoding.validExtensionCount
      (Encoding.directionMask (cliqueData dataSet)) root)
    Encoding.eight
boundaryExtensionCountAtMostEightLiteral dataSet =
  Encoding.boundaryExtensionCountAtMostEight
    (Encoding.directionMask (cliqueData dataSet))

interfaceExtensionCountAtMostEightLiteral dataSet =
  Encoding.interfaceExtensionCountAtMostEight
    (Encoding.directionMask (cliqueData dataSet))

cornerExtensionCountAtMostEightLiteral dataSet =
  Encoding.cornerExtensionCountAtMostEight
    (Encoding.directionMask (cliqueData dataSet))

nestedExtensionCountAtMostEightLiteral dataSet =
  Encoding.nestedExtensionCountAtMostEight
    (Encoding.directionMask (cliqueData dataSet))

physicalRootedExtensionsFormCliqueLiteral :
  ∀ {Polymer Block Root Tree Traversal}
    (dataSet : LiteralPhysicalPolymerCarrierInstance
      Polymer Block Root Tree Traversal)
    root first second →
  Encoding.literalValidExtension
    (Encoding.directionMask (cliqueData dataSet)) root first →
  Encoding.literalValidExtension
    (Encoding.directionMask (cliqueData dataSet)) root second →
  Encoding._#_
    (Encoding.literalExtensionPolymer
      (Encoding.literalRootedExtension
        (Encoding.extensionGeometry (cliqueData dataSet))
        (Encoding.rootBlockOf (cliqueData dataSet) root) first))
    (Encoding.literalExtensionPolymer
      (Encoding.literalRootedExtension
        (Encoding.extensionGeometry (cliqueData dataSet))
        (Encoding.rootBlockOf (cliqueData dataSet) root) second))
physicalRootedExtensionsFormCliqueLiteral dataSet =
  Encoding.physicalRootedExtensionsFormClique (cliqueData dataSet)

canonicalRootTreeTraversalReductionLevel : ProofLevel
canonicalRootTreeTraversalReductionLevel = machineChecked

physicalPatchMaskAdapterLevel : ProofLevel
physicalPatchMaskAdapterLevel = machineChecked

physicalCliqueAdapterLevel : ProofLevel
physicalCliqueAdapterLevel = machineChecked

literalPhysicalSpanningTreeInputsLevel : ProofLevel
literalPhysicalSpanningTreeInputsLevel = conditional

literalPhysicalDirectionMaskInputsLevel : ProofLevel
literalPhysicalDirectionMaskInputsLevel = conditional
