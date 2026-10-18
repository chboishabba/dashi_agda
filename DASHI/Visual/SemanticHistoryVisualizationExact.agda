module DASHI.Visual.SemanticHistoryVisualizationExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact
open import DASHI.Core.VersionedStateGraphExact
open import DASHI.Core.SemanticMergeEvolutionExact

------------------------------------------------------------------------
-- DECLARATIVE VISUALIZATION PROGRAM
--
-- Scenes are expressed as semantic commands.  Concrete Manim code is one
-- backend interpretation of this command language.
------------------------------------------------------------------------

data HistorySceneCommand : Set where
  showHistoryCommit : CommitNode → HistorySceneCommand
  showSemanticDelta : String → GraphDelta → HistorySceneCommand
  focusSemanticNode : String → HistorySceneCommand
  expandSemanticNode : String → HistorySceneCommand
  collapseSemanticNode : String → HistorySceneCommand
  moveSemanticNode : NodePlacement → String → HistorySceneCommand
  convergeSemanticParents :
    String →
    String →
    String →
    HistorySceneCommand

data SceneIntent : Set where
  commitVisibility : SceneIntent
  semanticChangeVisibility : SceneIntent
  semanticFocus : SceneIntent
  semanticExpansion : SceneIntent
  semanticCollapse : SceneIntent
  identityPreservingMotion : SceneIntent
  semanticMergeConvergence : SceneIntent

sceneIntent : HistorySceneCommand → SceneIntent
sceneIntent (showHistoryCommit _) = commitVisibility
sceneIntent (showSemanticDelta _ _) = semanticChangeVisibility
sceneIntent (focusSemanticNode _) = semanticFocus
sceneIntent (expandSemanticNode _) = semanticExpansion
sceneIntent (collapseSemanticNode _) = semanticCollapse
sceneIntent (moveSemanticNode _ _) = identityPreservingMotion
sceneIntent (convergeSemanticParents _ _ _) = semanticMergeConvergence

canonicalMoveCommand :
  NodePlacement →
  String →
  HistorySceneCommand
canonicalMoveCommand = moveSemanticNode

canonicalMoveCommandIsIdentityPreserving :
  ∀ placement slot →
  sceneIntent (canonicalMoveCommand placement slot)
    ≡ identityPreservingMotion
canonicalMoveCommandIsIdentityPreserving _ _ = refl

canonicalMergeCommand :
  String →
  String →
  String →
  HistorySceneCommand
canonicalMergeCommand = convergeSemanticParents

canonicalMergeCommandIsConvergence :
  ∀ left right merge →
  sceneIntent (canonicalMergeCommand left right merge)
    ≡ semanticMergeConvergence
canonicalMergeCommandIsConvergence _ _ _ = refl

record SemanticHistoryVisualizationBoundary : Set where
  constructor semanticHistoryVisualizationBoundary
  field
    sceneCommandsMayInventSemanticEdges : Bool
    sceneCommandsMayInventSemanticEdgesIsFalse :
      sceneCommandsMayInventSemanticEdges ≡ false

    sceneCommandsMayRewriteHistoryParents : Bool
    sceneCommandsMayRewriteHistoryParentsIsFalse :
      sceneCommandsMayRewriteHistoryParents ≡ false

    cameraFocusChangesSemanticState : Bool
    cameraFocusChangesSemanticStateIsFalse :
      cameraFocusChangesSemanticState ≡ false

canonicalSemanticHistoryVisualizationBoundary :
  SemanticHistoryVisualizationBoundary
canonicalSemanticHistoryVisualizationBoundary =
  semanticHistoryVisualizationBoundary
    false refl
    false refl
    false refl
