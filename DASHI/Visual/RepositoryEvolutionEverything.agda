module DASHI.Visual.RepositoryEvolutionEverything where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact
open import DASHI.Core.VersionedStateGraphExact
open import DASHI.Core.SemanticMergeEvolutionExact
open import DASHI.Core.SymbolIdentityEvolutionExact
open import DASHI.Core.NameResolutionAuthorityExact
open import DASHI.Core.ApplicationDependencyClassificationExact
open import DASHI.Core.LexicalScopeResolutionExact
open import DASHI.Core.LocalDeclarationScopeExact
open import DASHI.Core.IncrementalSemanticRelinkBoundaryExact
open import DASHI.Core.BackendSelectionPolicyExact
open import DASHI.Core.SemanticPatchBackendExact
open import DASHI.Core.PortableInteractiveViewExact
open import DASHI.Visual.SemanticHistoryVisualizationExact
open import DASHI.Visual.SemanticGraphProjectionExact
open import DASHI.Visual.SceneProgramCompilerExact
open import DASHI.Visual.RootedSemanticFocusExact
open import DASHI.Visual.TemporalRootedFocusExact
open import DASHI.Visual.EpisodeSalienceExact
open import DASHI.Visual.TraversalBudgetExact
open import DASHI.Visual.LayoutComplexityBoundaryExact
open import DASHI.Visual.TemporalAxisExact

------------------------------------------------------------------------
-- AGGREGATE CONTRACT FOR REPOSITORY-EVOLUTION VISUALIZATION
--
-- Concrete Tree-sitter/Git/Manim tooling is intentionally downstream of this
-- aggregate.  The formal surface records that history state and semantic
-- identity remain authoritative while rendering is a replaceable refinement.
------------------------------------------------------------------------

record RepositoryEvolutionBoundary : Set where
  constructor repositoryEvolutionBoundary
  field
    gitSpecificHistoryRequired : Bool
    gitSpecificHistoryRequiredIsFalse :
      gitSpecificHistoryRequired ≡ false

    multipleMaterializationsAllowed : Bool
    multipleMaterializationsAllowedIsTrue :
      multipleMaterializationsAllowed ≡ true

    branchMergeTopologyFirstClass : Bool
    branchMergeTopologyFirstClassIsTrue :
      branchMergeTopologyFirstClass ≡ true

    rendererMayInventDependencies : Bool
    rendererMayInventDependenciesIsFalse :
      rendererMayInventDependencies ≡ false

    rendererMayInventHistoryEdges : Bool
    rendererMayInventHistoryEdgesIsFalse :
      rendererMayInventHistoryEdges ≡ false

canonicalRepositoryEvolutionBoundary : RepositoryEvolutionBoundary
canonicalRepositoryEvolutionBoundary =
  repositoryEvolutionBoundary
    false refl
    true refl
    true refl
    false refl
    false refl

CanonicalBranchMergeVisualIntent : Set
CanonicalBranchMergeVisualIntent =
  historyPrimitiveIntent
    (compileHistoryEvent
      (forkObserved canonicalForkWitness))
  ≡
  branchLaneSplits

canonicalBranchMergeVisualIntent :
  CanonicalBranchMergeVisualIntent
canonicalBranchMergeVisualIntent = refl

CanonicalMergeVisualIntent : Set
CanonicalMergeVisualIntent =
  historyPrimitiveIntent
    (compileHistoryEvent
      (mergeObserved canonicalMergeWitness))
  ≡
  branchLanesJoin

canonicalMergeVisualIntent :
  CanonicalMergeVisualIntent
canonicalMergeVisualIntent = refl
