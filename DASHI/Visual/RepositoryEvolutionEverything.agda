module DASHI.Visual.RepositoryEvolutionEverything where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact
open import DASHI.Core.VersionedStateGraphExact
open import DASHI.Core.SemanticMergeEvolutionExact
open import DASHI.Core.PortableInteractiveViewExact
open import DASHI.Visual.SemanticHistoryVisualizationExact

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
