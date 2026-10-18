module DASHI.Visual.ActiveWorkingSetExact where

open import DASHI.Core.Prelude

record ActiveWorkingSet : Set where
  constructor activeWorkingSet
  field
    activeCommitId : String
    activeProgramme : String
    activeTopicTokens : List String
    changedNodeIds : List String
    changedEdgeIds : List String
    contextNodeIds : List String
    contextEdgeIds : List String
    activeModules : List String
    activeChangedSymbolLabels : List String
    activeLaneHint : String
    activeHeadline : String
    activeSalience : Nat

open ActiveWorkingSet public

record ActiveWorkingSetBoundary : Set where
  constructor activeWorkingSetBoundary
  field
    unchangedWholeRepositoryIsActiveByDefault : Bool
    unchangedWholeRepositoryIsActiveByDefaultIsFalse :
      unchangedWholeRepositoryIsActiveByDefault ≡ false

    contextMayInventSemanticDependency : Bool
    contextMayInventSemanticDependencyIsFalse :
      contextMayInventSemanticDependency ≡ false

    changedSemanticObjectsRemainPrimary : Bool
    changedSemanticObjectsRemainPrimaryIsTrue :
      changedSemanticObjectsRemainPrimary ≡ true

    explanatoryMetadataMayCreateSemanticEdges : Bool
    explanatoryMetadataMayCreateSemanticEdgesIsFalse :
      explanatoryMetadataMayCreateSemanticEdges ≡ false

    truncatedWindowCheckpointMeansMassCreation : Bool
    truncatedWindowCheckpointMeansMassCreationIsFalse :
      truncatedWindowCheckpointMeansMassCreation ≡ false

canonicalActiveWorkingSetBoundary : ActiveWorkingSetBoundary
canonicalActiveWorkingSetBoundary =
  activeWorkingSetBoundary
    false refl
    false refl
    true refl
    false refl
    false refl
