module DASHI.Reasoning.AristotleMergeExperimentDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Reasoning.AristotleBranchMergeExact as Merge

------------------------------------------------------------------------
-- ARISTOTLE MERGE x EXPERIMENT DESIGN
--
-- Proof-search uncertainty is treated here as an information-design problem:
-- a visible MCGS state can leave several branch histories compatible.  The
-- relevant experiment is whatever typed discriminator resolves the collision
-- needed by the downstream consumer (here: whether branch merge is admissible).
--
-- This consumes the repository's existing experiment-design calculus.  It
-- does not claim that theorem proving is literally a laboratory experiment.
------------------------------------------------------------------------

BranchWorld : Set
BranchWorld =
  Merge.BranchSnapshot
    Merge.Surface
    Merge.DependencyCode
    Merge.ProvenanceCode
    Merge.Lemma

coarseProofObserver : BranchWorld → Merge.Surface
coarseProofObserver = Merge.visible

dependencyObserver : BranchWorld → Merge.DependencyCode
dependencyObserver = Merge.dependency

provenanceObserver : BranchWorld → Merge.ProvenanceCode
provenanceObserver = Merge.provenance

------------------------------------------------------------------------
-- Merge decision as the declared consumer.
------------------------------------------------------------------------

data MergeDecision : Set where
  mergeAdmissible refineBeforeMerge : MergeDecision

mergeDecisionCode :
  Merge.DependencyCode × Merge.ProvenanceCode → MergeDecision
mergeDecisionCode
  (Merge.localDependency , Merge.inheritedHistory) = mergeAdmissible
mergeDecisionCode _ = refineBeforeMerge

guardObserver : BranchWorld → Merge.DependencyCode × Merge.ProvenanceCode
guardObserver branch = dependencyObserver branch , provenanceObserver branch

mergeDecision : BranchWorld → MergeDecision
mergeDecision branch = mergeDecisionCode (guardObserver branch)

mergeDecisionCongruent :
  ∀ left right →
  dependencyObserver left ≡ dependencyObserver right →
  provenanceObserver left ≡ provenanceObserver right →
  mergeDecision left ≡ mergeDecision right
mergeDecisionCongruent left right sameDependency sameProvenance =
  cong mergeDecisionCode (Consumer.pairEquality sameDependency sameProvenance)

-- The joint hidden-coordinate observer is sufficient for the merge consumer.
guardObserverSufficientForMergeDecision :
  Consumer.ConsumerSufficient guardObserver mergeDecision
guardObserverSufficientForMergeDecision left right sameGuard =
  cong mergeDecisionCode sameGuard

mergeDecisionResidualRepair :
  Consumer.ResidualRepair coarseProofObserver guardObserver mergeDecision
mergeDecisionResidualRepair =
  Consumer.residual-repair guardObserverSufficientForMergeDecision

------------------------------------------------------------------------
-- The existing visible observer has consumer-relevant collisions.
------------------------------------------------------------------------

dependencyMergeCollision :
  Consumer.ConsumerRelevantCollision coarseProofObserver mergeDecision
dependencyMergeCollision =
  Consumer.consumer-relevant-collision
    Merge.leftBranch
    Merge.hiddenDependencyBranch
    refl
    (λ ())

provenanceMergeCollision :
  Consumer.ConsumerRelevantCollision coarseProofObserver mergeDecision
provenanceMergeCollision =
  Consumer.consumer-relevant-collision
    Merge.leftBranch
    Merge.reintroducedProvenanceBranch
    refl
    (λ ())

coarseObserverCannotCloseMergeDecision :
  Consumer.ConsumerSufficient coarseProofObserver mergeDecision → ⊥
coarseObserverCannotCloseMergeDecision =
  Consumer.coarseCollisionBlocksSufficiency dependencyMergeCollision

------------------------------------------------------------------------
-- Experiment bundles are proof-search probes.
------------------------------------------------------------------------

dependencyProbe : Synthesis.ExperimentBundle BranchWorld
dependencyProbe =
  Synthesis.experimentBundle
    Merge.DependencyCode
    dependencyObserver
    1
    "proof-search dependency probe"
    "DASHI residual-dependency coordinate"

provenanceProbe : Synthesis.ExperimentBundle BranchWorld
provenanceProbe =
  Synthesis.experimentBundle
    Merge.ProvenanceCode
    provenanceObserver
    1
    "proof-search provenance probe"
    "DASHI coordinate-lineage/provenance coordinate"

guardProbe : Synthesis.ExperimentBundle BranchWorld
guardProbe =
  Synthesis.experimentBundle
    (Merge.DependencyCode × Merge.ProvenanceCode)
    guardObserver
    2
    "joint proof-search merge guard probe"
    "dependency plus provenance discriminator"

dependencyProbeSeparatesHiddenDependencyCollision :
  Synthesis.BundleSeparates
    dependencyProbe
    Merge.leftBranch
    Merge.hiddenDependencyBranch
dependencyProbeSeparatesHiddenDependencyCollision =
  Synthesis.bundleSeparates Merge.localIsNotGlobalSensitive

provenanceProbeSeparatesLineageCollision :
  Synthesis.BundleSeparates
    provenanceProbe
    Merge.leftBranch
    Merge.reintroducedProvenanceBranch
provenanceProbeSeparatesLineageCollision =
  Synthesis.bundleSeparates Merge.inheritedIsNotIntroduced

dependencyLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension coarseProofObserver
dependencyLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    (Synthesis.currentObserverCollision
      Merge.leftBranch
      Merge.hiddenDependencyBranch
      refl)
    dependencyProbe
    dependencyProbeSeparatesHiddenDependencyCollision

provenanceLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension coarseProofObserver
provenanceLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    (Synthesis.currentObserverCollision
      Merge.leftBranch
      Merge.reintroducedProvenanceBranch
      refl)
    provenanceProbe
    provenanceProbeSeparatesLineageCollision

------------------------------------------------------------------------
-- A genuine outcome-adaptive sequential plan.
--
-- First ask the dependency question.
--
--   global-sensitive dependency -> merge is already ruled out, close.
--   local dependency            -> ask provenance next.
--
-- Thus the next proof-search experiment depends on the observed result, exactly
-- matching the generic sequential planner already used elsewhere in DASHI.
------------------------------------------------------------------------

allBranchesLive : BranchWorld → Set
allBranchesLive branch = ⊤

globalDependencyForcesRefinement :
  ∀ branch →
  dependencyObserver branch ≡ Merge.globalSensitiveDependency →
  mergeDecision branch ≡ refineBeforeMerge
globalDependencyForcesRefinement branch same with dependencyObserver branch
... | Merge.localDependency with same
...   | ()
... | Merge.globalSensitiveDependency = refl

localInheritedAllowsMerge :
  ∀ branch →
  dependencyObserver branch ≡ Merge.localDependency →
  provenanceObserver branch ≡ Merge.inheritedHistory →
  mergeDecision branch ≡ mergeAdmissible
localInheritedAllowsMerge branch sameDependency sameProvenance
  with dependencyObserver branch | provenanceObserver branch
... | Merge.localDependency | Merge.inheritedHistory = refl
... | Merge.localDependency | Merge.introducedHistory with sameProvenance
...   | ()
... | Merge.globalSensitiveDependency | provenance with sameDependency
...   | ()

localIntroducedForcesRefinement :
  ∀ branch →
  dependencyObserver branch ≡ Merge.localDependency →
  provenanceObserver branch ≡ Merge.introducedHistory →
  mergeDecision branch ≡ refineBeforeMerge
localIntroducedForcesRefinement branch sameDependency sameProvenance
  with dependencyObserver branch | provenanceObserver branch
... | Merge.localDependency | Merge.inheritedHistory with sameProvenance
...   | ()
... | Merge.localDependency | Merge.introducedHistory = refl
... | Merge.globalSensitiveDependency | provenance with sameDependency
...   | ()

provenanceContinuation :
  (outcome : Merge.ProvenanceCode) →
  Planner.OutcomePossible
    (Planner.RefineByBundle allBranchesLive dependencyProbe Merge.localDependency)
    provenanceProbe
    outcome →
  Planner.SequentialConsumerPlan
    mergeDecision
    (Planner.RefineByBundle
      (Planner.RefineByBundle allBranchesLive dependencyProbe Merge.localDependency)
      provenanceProbe
      outcome)
provenanceContinuation outcome possible =
  Planner.closeConsumer λ left right leftLive rightLive →
    mergeDecisionCongruent
      left right
      (trans (proj₂ (proj₁ leftLive)) (sym (proj₂ (proj₁ rightLive))))
      (trans (proj₂ leftLive) (sym (proj₂ rightLive)))

dependencyContinuation :
  (outcome : Merge.DependencyCode) →
  Planner.OutcomePossible allBranchesLive dependencyProbe outcome →
  Planner.SequentialConsumerPlan
    mergeDecision
    (Planner.RefineByBundle allBranchesLive dependencyProbe outcome)
dependencyContinuation Merge.localDependency possible =
  Planner.askThen provenanceProbe provenanceContinuation
dependencyContinuation Merge.globalSensitiveDependency possible =
  Planner.closeConsumer λ left right leftLive rightLive →
    trans
      (globalDependencyForcesRefinement left (proj₂ leftLive))
      (sym (globalDependencyForcesRefinement right (proj₂ rightLive)))

dependencyThenProvenancePlan :
  Planner.SequentialConsumerPlan mergeDecision allBranchesLive
dependencyThenProvenancePlan =
  Planner.askThen dependencyProbe dependencyContinuation

------------------------------------------------------------------------
-- A joint one-shot plan exists too; the sequential plan can be cheaper on a
-- branch because global-sensitive dependency does not need a provenance probe.
------------------------------------------------------------------------

guardProbePlan :
  Planner.SequentialConsumerPlan mergeDecision allBranchesLive
guardProbePlan =
  Planner.askThen guardProbe λ outcome possible →
    Planner.closeConsumer λ left right leftLive rightLive →
      guardObserverSufficientForMergeDecision
        left right
        (trans (proj₂ leftLive) (sym (proj₂ rightLive)))

------------------------------------------------------------------------
-- Residual-dependency cross-pollination theorem: a hidden dependency collision
-- is already exactly a strict observer-refinement signal in the canonical core.
------------------------------------------------------------------------

hiddenResidualDependencyDemandsRefinement :
  ∀ {State Action Index Code Coarse : Set}
    {dependency : Residual.ResidualDependencyObserver State Action Index Code}
    {coarse : State → Coarse}
    {action : Action} →
  Residual.HiddenResidualDependency dependency coarse action →
  DASHI.Core.ObserverRefinementLatticeExact.StrictRefinement
    coarse
    (Residual.refinedObservationAt dependency coarse action)
hiddenResidualDependencyDemandsRefinement =
  Residual.hiddenResidualDependencyGivesStrictRefinement

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AristotleMergeExperimentBoundary : Set where
  constructor aristotleMergeExperimentBoundary
  field
    proofSearchProbeMustIdentifyWholeHiddenWorld : Bool
    proofSearchProbeMustIdentifyWholeHiddenWorldIsFalse :
      proofSearchProbeMustIdentifyWholeHiddenWorld ≡ false

    nextProofSearchProbeMayDependOnOutcome : Bool
    nextProofSearchProbeMayDependOnOutcomeIsTrue :
      nextProofSearchProbeMayDependOnOutcome ≡ true

    visibleGoalEqualityClosesMergeDecision : Bool
    visibleGoalEqualityClosesMergeDecisionIsFalse :
      visibleGoalEqualityClosesMergeDecision ≡ false

    hiddenDependencyCanBeAConsumerRelevantDiscriminator : Bool
    hiddenDependencyCanBeAConsumerRelevantDiscriminatorIsTrue :
      hiddenDependencyCanBeAConsumerRelevantDiscriminator ≡ true

    provenanceCanBeASecondStageDiscriminator : Bool
    provenanceCanBeASecondStageDiscriminatorIsTrue :
      provenanceCanBeASecondStageDiscriminator ≡ true

    proofSearchIsClaimedToBeLiteralPhysicalExperiment : Bool
    proofSearchIsClaimedToBeLiteralPhysicalExperimentIsFalse :
      proofSearchIsClaimedToBeLiteralPhysicalExperiment ≡ false

    reading : String

canonicalAristotleMergeExperimentBoundary : AristotleMergeExperimentBoundary
canonicalAristotleMergeExperimentBoundary =
  aristotleMergeExperimentBoundary
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    "Aristotle/DASHI proof search as sequential information design: resolve only consumer-relevant branch collisions; dependency can close rejection immediately, while a compatible dependency outcome can trigger a provenance probe before merge."
