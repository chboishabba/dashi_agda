module DASHI.Reasoning.AristotleMergeExperimentDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.ResidualObserverDependencyExact as Residual
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Reasoning.AristotleBranchMergeExact as Merge

------------------------------------------------------------------------
-- ARISTOTLE MERGE x EXPERIMENT DESIGN
--
-- Proof-search uncertainty is treated here as an information-design problem:
-- a visible MCGS state can leave several branch histories compatible.  The
-- relevant experiment is whatever typed discriminator resolves the collision
-- needed by the downstream consumer (here: whether branch merge is admissible).
--
-- The proof-bearing `BranchSnapshot` lives in Set1 because its knowledge field
-- is proposition-valued.  The generic experiment planner intentionally takes a
-- first-order `World : Set`.  We therefore use a finite branch-world specimen
-- and an explicit `snapshotOf` map into the merge layer, rather than silently
-- identifying those carriers.
------------------------------------------------------------------------

data BranchWorld : Set where
  leftWorld compatibleWorld hiddenDependencyWorld reintroducedWorld : BranchWorld

snapshotOf :
  BranchWorld →
  Merge.BranchSnapshot
    Merge.Surface
    Merge.DependencyCode
    Merge.ProvenanceCode
    Merge.Lemma
snapshotOf leftWorld = Merge.leftBranch
snapshotOf compatibleWorld = Merge.compatibleRightBranch
snapshotOf hiddenDependencyWorld = Merge.hiddenDependencyBranch
snapshotOf reintroducedWorld = Merge.reintroducedProvenanceBranch

coarseProofObserver : BranchWorld → Merge.Surface
coarseProofObserver world = Merge.visible (snapshotOf world)

dependencyObserver : BranchWorld → Merge.DependencyCode
dependencyObserver world = Merge.dependency (snapshotOf world)

provenanceObserver : BranchWorld → Merge.ProvenanceCode
provenanceObserver world = Merge.provenance (snapshotOf world)

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
guardObserver world = dependencyObserver world , provenanceObserver world

mergeDecision : BranchWorld → MergeDecision
mergeDecision world = mergeDecisionCode (guardObserver world)

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
    leftWorld
    hiddenDependencyWorld
    refl
    (λ ())

provenanceMergeCollision :
  Consumer.ConsumerRelevantCollision coarseProofObserver mergeDecision
provenanceMergeCollision =
  Consumer.consumer-relevant-collision
    leftWorld
    reintroducedWorld
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
    leftWorld
    hiddenDependencyWorld
dependencyProbeSeparatesHiddenDependencyCollision =
  Synthesis.bundleSeparates Merge.localIsNotGlobalSensitive

provenanceProbeSeparatesLineageCollision :
  Synthesis.BundleSeparates
    provenanceProbe
    leftWorld
    reintroducedWorld
provenanceProbeSeparatesLineageCollision =
  Synthesis.bundleSeparates Merge.inheritedIsNotIntroduced

dependencyLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension coarseProofObserver
dependencyLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    (Synthesis.currentObserverCollision
      leftWorld
      hiddenDependencyWorld
      refl)
    dependencyProbe
    dependencyProbeSeparatesHiddenDependencyCollision

provenanceLanguageExtension :
  Synthesis.DiscriminatingLanguageExtension coarseProofObserver
provenanceLanguageExtension =
  Synthesis.discriminatingLanguageExtension
    (Synthesis.currentObserverCollision
      leftWorld
      reintroducedWorld
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
allBranchesLive world = ⊤

globalDependencyForcesRefinement :
  ∀ world →
  dependencyObserver world ≡ Merge.globalSensitiveDependency →
  mergeDecision world ≡ refineBeforeMerge
globalDependencyForcesRefinement leftWorld ()
globalDependencyForcesRefinement compatibleWorld ()
globalDependencyForcesRefinement hiddenDependencyWorld refl = refl
globalDependencyForcesRefinement reintroducedWorld ()

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
    {coarse : Observer.Observer State Coarse}
    {action : Action} →
  Residual.HiddenResidualDependency dependency coarse action →
  Observer.StrictRefinement
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
