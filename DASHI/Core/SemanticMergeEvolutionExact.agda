module DASHI.Core.SemanticMergeEvolutionExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact
open import DASHI.Core.VersionedStateGraphExact

------------------------------------------------------------------------
-- PARENT-RELATIVE SEMANTIC EVOLUTION
--
-- A merge commit is not compared to an arbitrary previous frame.  Each parent
-- has its own semantic delta into the merge result.  This is the formal
-- surface consumed by the history renderer.
------------------------------------------------------------------------

record ParentSemanticDelta : Set where
  constructor parentSemanticDelta
  field
    semanticParentId : String
    semanticParentDelta : GraphDelta

open ParentSemanticDelta public

record MergeSemanticObservation : Set where
  constructor mergeSemanticObservation
  field
    semanticMergeCommit : CommitNode
    semanticMergeGraph : SemanticGraph
    semanticParentDeltas : List ParentSemanticDelta

open MergeSemanticObservation public

data MergeContributionKind : Set where
  inheritedFromParent : MergeContributionKind
  introducedAtMerge : MergeContributionKind
  removedAtMerge : MergeContributionKind
  reconciledAtMerge : MergeContributionKind

record MergeContribution : Set where
  constructor mergeContribution
  field
    contributionSymbolId : String
    contributionKind : MergeContributionKind

open MergeContribution public

------------------------------------------------------------------------
-- Renderer-neutral merge actions.
------------------------------------------------------------------------

data MergeVisualPrimitive : Set where
  showParentDelta :
    ParentSemanticDelta →
    MergeVisualPrimitive

  convergeParentGraphs :
    String →
    String →
    String →
    MergeVisualPrimitive

  showMergeContribution :
    MergeContribution →
    MergeVisualPrimitive

data MergeVisualIntent : Set where
  parentDeltaAppears : MergeVisualIntent
  semanticBranchesConverge : MergeVisualIntent
  mergeContributionAppears : MergeVisualIntent

mergeVisualIntent : MergeVisualPrimitive → MergeVisualIntent
mergeVisualIntent (showParentDelta _) = parentDeltaAppears
mergeVisualIntent (convergeParentGraphs _ _ _) = semanticBranchesConverge
mergeVisualIntent (showMergeContribution _) = mergeContributionAppears

compileParentDelta :
  ParentSemanticDelta →
  MergeVisualPrimitive
compileParentDelta = showParentDelta

compileParentDeltaIntentExact :
  ∀ parentDelta →
  mergeVisualIntent (compileParentDelta parentDelta)
    ≡ parentDeltaAppears
compileParentDeltaIntentExact _ = refl

compileMergeConvergence :
  (leftParent rightParent mergeId : String) →
  MergeVisualPrimitive
compileMergeConvergence = convergeParentGraphs

compileMergeConvergenceIntentExact :
  ∀ leftParent rightParent mergeId →
  mergeVisualIntent
    (compileMergeConvergence leftParent rightParent mergeId)
    ≡ semanticBranchesConverge
compileMergeConvergenceIntentExact _ _ _ = refl

------------------------------------------------------------------------
-- Identity is semantic, not positional.
------------------------------------------------------------------------

record NodePlacement : Set where
  constructor nodePlacement
  field
    placedSymbolId : String
    layoutSlotId : String

open NodePlacement public

movePlacement :
  NodePlacement →
  String →
  NodePlacement
movePlacement placement newSlot =
  nodePlacement
    (placedSymbolId placement)
    newSlot

movePlacementPreservesIdentity :
  ∀ placement newSlot →
  placedSymbolId (movePlacement placement newSlot)
    ≡ placedSymbolId placement
movePlacementPreservesIdentity _ _ = refl

record SemanticMergeEvolutionBoundary : Set where
  constructor semanticMergeEvolutionBoundary
  field
    mergeDeltaMayUseArbitraryPreviousFrame : Bool
    mergeDeltaMayUseArbitraryPreviousFrameIsFalse :
      mergeDeltaMayUseArbitraryPreviousFrame ≡ false

    layoutMotionMayChangeSemanticIdentity : Bool
    layoutMotionMayChangeSemanticIdentityIsFalse :
      layoutMotionMayChangeSemanticIdentity ≡ false

    mergeAttributionRequiresParentRelativeEvidence : Bool
    mergeAttributionRequiresParentRelativeEvidenceIsTrue :
      mergeAttributionRequiresParentRelativeEvidence ≡ true

canonicalSemanticMergeEvolutionBoundary :
  SemanticMergeEvolutionBoundary
canonicalSemanticMergeEvolutionBoundary =
  semanticMergeEvolutionBoundary
    false refl
    false refl
    true refl
