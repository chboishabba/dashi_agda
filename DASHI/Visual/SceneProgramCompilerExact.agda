module DASHI.Visual.SceneProgramCompilerExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact
open import DASHI.Core.VersionedStateGraphExact
open import DASHI.Core.SemanticMergeEvolutionExact
open import DASHI.Visual.SemanticHistoryVisualizationExact
open import DASHI.Visual.RootedSemanticFocusExact
open import DASHI.Visual.TemporalRootedFocusExact

------------------------------------------------------------------------
-- SCENE PROGRAM COMPILER
--
-- History/semantic observations compile to a renderer-neutral command stream.
-- Manim interprets that stream; it does not infer a different history.
------------------------------------------------------------------------

data DeltaSceneCommand : Set where
  deltaAddNode : SymbolNode → DeltaSceneCommand
  deltaRemoveNode : String → DeltaSceneCommand
  deltaAddEdge : SemanticEdge → DeltaSceneCommand
  deltaRemoveEdge : SemanticEdge → DeltaSceneCommand
  deltaRenameNode : String → String → DeltaSceneCommand
  deltaReplaceGraph : SemanticGraph → DeltaSceneCommand

deltaSceneIntent : DeltaSceneCommand → DeltaIntent
deltaSceneIntent (deltaAddNode _) = nodeAppears
deltaSceneIntent (deltaRemoveNode _) = nodeDisappears
deltaSceneIntent (deltaAddEdge _) = edgeAppears
deltaSceneIntent (deltaRemoveEdge _) = edgeDisappears
deltaSceneIntent (deltaRenameNode _ _) = nodeIdentityChanges
deltaSceneIntent (deltaReplaceGraph _) = graphStateChanges

compileGraphDeltaCommand : GraphDelta → DeltaSceneCommand
compileGraphDeltaCommand (addNode node) = deltaAddNode node
compileGraphDeltaCommand (removeNode nodeId) = deltaRemoveNode nodeId
compileGraphDeltaCommand (addEdge edge) = deltaAddEdge edge
compileGraphDeltaCommand (removeEdge edge) = deltaRemoveEdge edge
compileGraphDeltaCommand (renameNode old new) =
  deltaRenameNode old new
compileGraphDeltaCommand (replaceGraph graph) =
  deltaReplaceGraph graph

compileGraphDeltaCommandIntentExact :
  ∀ delta →
  deltaSceneIntent (compileGraphDeltaCommand delta)
    ≡ deltaIntent delta
compileGraphDeltaCommandIntentExact (addNode _) = refl
compileGraphDeltaCommandIntentExact (removeNode _) = refl
compileGraphDeltaCommandIntentExact (addEdge _) = refl
compileGraphDeltaCommandIntentExact (removeEdge _) = refl
compileGraphDeltaCommandIntentExact (renameNode _ _) = refl
compileGraphDeltaCommandIntentExact (replaceGraph _) = refl

data EpisodeSceneCommand : Set where
  showForkEpisode :
    BranchMergeEpisode →
    EpisodeSceneCommand

  showParentSemanticDelta :
    ParentSemanticDelta →
    EpisodeSceneCommand

  convergeEpisode :
    String →
    String →
    String →
    EpisodeSceneCommand

data EpisodeSceneIntent : Set where
  forkEpisodeAppears : EpisodeSceneIntent
  parentSemanticChangeAppears : EpisodeSceneIntent
  episodeConverges : EpisodeSceneIntent

episodeSceneIntent : EpisodeSceneCommand → EpisodeSceneIntent
episodeSceneIntent (showForkEpisode _) = forkEpisodeAppears
episodeSceneIntent (showParentSemanticDelta _) =
  parentSemanticChangeAppears
episodeSceneIntent (convergeEpisode _ _ _) = episodeConverges

compileParentSemanticDeltaCommand :
  ParentSemanticDelta →
  EpisodeSceneCommand
compileParentSemanticDeltaCommand = showParentSemanticDelta

compileParentSemanticDeltaCommandIntentExact :
  ∀ parentDelta →
  episodeSceneIntent
    (compileParentSemanticDeltaCommand parentDelta)
  ≡ parentSemanticChangeAppears
compileParentSemanticDeltaCommandIntentExact _ = refl

compileEpisodeConvergenceCommand :
  (left right merge : String) →
  EpisodeSceneCommand
compileEpisodeConvergenceCommand = convergeEpisode

compileEpisodeConvergenceCommandIntentExact :
  ∀ left right merge →
  episodeSceneIntent
    (compileEpisodeConvergenceCommand left right merge)
  ≡ episodeConverges
compileEpisodeConvergenceCommandIntentExact _ _ _ = refl

record SceneProgramCompilerBoundary : Set where
  constructor sceneProgramCompilerBoundary
  field
    backendMayReorderParentRelativeDeltas : Bool
    backendMayReorderParentRelativeDeltasIsFalse :
      backendMayReorderParentRelativeDeltas ≡ false

    backendMayReplaceParentWithTopoNeighbour : Bool
    backendMayReplaceParentWithTopoNeighbourIsFalse :
      backendMayReplaceParentWithTopoNeighbour ≡ false

    commandStreamMayInventSemanticObjects : Bool
    commandStreamMayInventSemanticObjectsIsFalse :
      commandStreamMayInventSemanticObjects ≡ false

canonicalSceneProgramCompilerBoundary :
  SceneProgramCompilerBoundary
canonicalSceneProgramCompilerBoundary =
  sceneProgramCompilerBoundary
    false refl
    false refl
    false refl


------------------------------------------------------------------------
-- ROOTED / TEMPORAL FOCUS PROGRAM COMMANDS
------------------------------------------------------------------------

data FocusSceneCommand : Set where
  showCompiledFocusRoot :
    RootedSemanticFocus →
    FocusSceneCommand

  expandCompiledFocusLayer :
    Nat →
    FocusSceneCommand

  settleCompiledFocus :
    RootedSemanticFocus →
    FocusSceneCommand

  showCompiledTemporalFocus :
    TemporalFocusFrame →
    FocusSceneCommand

  advanceCompiledTemporalFocus :
    TemporalFocusFrame →
    FocusSceneCommand

data FocusSceneCommandIntent : Set where
  compiledFocusRootAppears : FocusSceneCommandIntent
  compiledFocusLayerExpands : FocusSceneCommandIntent
  compiledFocusSettles : FocusSceneCommandIntent
  compiledTemporalFocusAppears : FocusSceneCommandIntent
  compiledTemporalFocusAdvances : FocusSceneCommandIntent

focusSceneCommandIntent :
  FocusSceneCommand →
  FocusSceneCommandIntent
focusSceneCommandIntent (showCompiledFocusRoot _) =
  compiledFocusRootAppears
focusSceneCommandIntent (expandCompiledFocusLayer _) =
  compiledFocusLayerExpands
focusSceneCommandIntent (settleCompiledFocus _) =
  compiledFocusSettles
focusSceneCommandIntent (showCompiledTemporalFocus _) =
  compiledTemporalFocusAppears
focusSceneCommandIntent (advanceCompiledTemporalFocus _) =
  compiledTemporalFocusAdvances

compileFocusRootCommand :
  RootedSemanticFocus →
  FocusSceneCommand
compileFocusRootCommand = showCompiledFocusRoot

compileFocusRootCommandIntentExact :
  ∀ focus →
  focusSceneCommandIntent (compileFocusRootCommand focus)
    ≡ compiledFocusRootAppears
compileFocusRootCommandIntentExact _ = refl

compileTemporalFocusAdvanceCommand :
  TemporalFocusFrame →
  FocusSceneCommand
compileTemporalFocusAdvanceCommand =
  advanceCompiledTemporalFocus

compileTemporalFocusAdvanceCommandIntentExact :
  ∀ frame →
  focusSceneCommandIntent
    (compileTemporalFocusAdvanceCommand frame)
  ≡ compiledTemporalFocusAdvances
compileTemporalFocusAdvanceCommandIntentExact _ = refl

record FocusSceneProgramBoundary : Set where
  constructor focusSceneProgramBoundary
  field
    focusProgramMayInventTraversalLayer : Bool
    focusProgramMayInventTraversalLayerIsFalse :
      focusProgramMayInventTraversalLayer ≡ false

    temporalProgramMayInventIdentityTransition : Bool
    temporalProgramMayInventIdentityTransitionIsFalse :
      temporalProgramMayInventIdentityTransition ≡ false

    backendMayRecomputeDifferentFocusAuthority : Bool
    backendMayRecomputeDifferentFocusAuthorityIsFalse :
      backendMayRecomputeDifferentFocusAuthority ≡ false

canonicalFocusSceneProgramBoundary :
  FocusSceneProgramBoundary
canonicalFocusSceneProgramBoundary =
  focusSceneProgramBoundary
    false refl
    false refl
    false refl
