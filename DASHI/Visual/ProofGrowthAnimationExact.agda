module DASHI.Visual.ProofGrowthAnimationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- PROOF-GROWTH ANIMATION
--
-- A newly visible semantic object may visually emerge from an already-visible
-- semantic neighbour only when an admitted relation connects them. Rendering
-- may choose which admitted relation is most explanatory; it may not fabricate
-- a precursor.
------------------------------------------------------------------------

data ProofRevealKind : Set where
  revealFromSemanticNeighbour : ProofRevealKind
  revealUnanchored : ProofRevealKind

record ProofReveal : Set where
  constructor proofReveal
  field
    revealNodeId : String
    revealKind : ProofRevealKind
    revealPrecursorNodeId : String

open ProofReveal public

record ProofGrowthAnimationBoundary : Set where
  constructor proofGrowthAnimationBoundary
  field
    rendererMayInventPrecursorRelation : Bool
    rendererMayInventPrecursorRelationIsFalse :
      rendererMayInventPrecursorRelation ≡ false

    admittedDependencyMayGuideTransformFromCopy : Bool
    admittedDependencyMayGuideTransformFromCopyIsTrue :
      admittedDependencyMayGuideTransformFromCopy ≡ true

    unanchoredNodeMayStillAppear : Bool
    unanchoredNodeMayStillAppearIsTrue :
      unanchoredNodeMayStillAppear ≡ true

canonicalProofGrowthAnimationBoundary :
  ProofGrowthAnimationBoundary
canonicalProofGrowthAnimationBoundary =
  proofGrowthAnimationBoundary
    false refl
    true refl
    true refl
