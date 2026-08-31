module DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Reasoning.AristotleBranchMergeExact as Merge
import DASHI.Reasoning.AristotleMergeExperimentDesignExact as Experiment
import DASHI.Reasoning.AristotleMergeGovernanceCrossPollinationExact as Governance

------------------------------------------------------------------------
-- ACTIVE EXPERIMENTAL PROOF-SEARCH LOOP
--
-- This owner packages the cross-pollinated DASHI construction suggested by the
-- Aristotle MCGS substrate:
--
--   live proof hypotheses
--   -> consumer-relevant collision
--   -> discriminator synthesis
--   -> tactic/lemma/observer experiment
--   -> live-fibre refinement
--   -> guarded merge of compatible discoveries
--   -> selective reopening along reverse dependency closure
--   -> iterate, or close when the declared consumer is constant.
--
-- Aristotle's paper remains the authority only for its MCGS search hypergraph
-- and formal-feedback semantics.  The active-experiment, merge, provenance,
-- reopening and governance loop below is a DASHI construction.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Experimental coordinate view of the finite branch world.
------------------------------------------------------------------------

data ProbeControl : Set where
  inspectDependency inspectProvenance inspectBoth : ProbeControl

data CoordinateId : Set where
  visibleCoordinate dependencyCoordinate provenanceCoordinate : CoordinateId

data CoordinateValue : Set where
  visibleValue : Merge.Surface → CoordinateValue
  dependencyValue : Merge.DependencyCode → CoordinateValue
  provenanceValue : Merge.ProvenanceCode → CoordinateValue

data CoordinateDimension : Set where
  proofSurfaceDimension dependencyDimension provenanceDimension : CoordinateDimension

applyProbe : ProbeControl → Experiment.BranchWorld → Experiment.BranchWorld
applyProbe control world = world

readCoordinate : CoordinateId → Experiment.BranchWorld → CoordinateValue
readCoordinate visibleCoordinate world =
  visibleValue (Experiment.coarseProofObserver world)
readCoordinate dependencyCoordinate world =
  dependencyValue (Experiment.dependencyObserver world)
readCoordinate provenanceCoordinate world =
  provenanceValue (Experiment.provenanceObserver world)

proofSearchCoordinateDesign :
  Coordinate.ExperimentalCoordinateDesign
    Experiment.BranchWorld ProbeControl CoordinateValue CoordinateDimension
proofSearchCoordinateDesign =
  Coordinate.experimentalCoordinateDesign
    CoordinateId
    role
    dimension
    readCoordinate
    applyProbe
    coordinateReference
    dimensionReference
    calibrationReference
    controlReference
  where
    role : CoordinateId → Coordinate.CoordinateRole
    role visibleCoordinate = Coordinate.measuredObservable
    role dependencyCoordinate = Coordinate.derivedDiscriminator
    role provenanceCoordinate = Coordinate.derivedDiscriminator

    dimension : CoordinateId → CoordinateDimension
    dimension visibleCoordinate = proofSurfaceDimension
    dimension dependencyCoordinate = dependencyDimension
    dimension provenanceCoordinate = provenanceDimension

    coordinateReference : CoordinateId → String
    coordinateReference visibleCoordinate = "Aristotle visible proof-state observer"
    coordinateReference dependencyCoordinate = "DASHI residual dependency discriminator"
    coordinateReference provenanceCoordinate = "DASHI governed provenance discriminator"

    dimensionReference : CoordinateId → String
    dimensionReference visibleCoordinate = "proof-state surface coordinate"
    dimensionReference dependencyCoordinate = "action-relevant dependency coordinate"
    dimensionReference provenanceCoordinate = "branch-lineage coordinate"

    calibrationReference : CoordinateId → String
    calibrationReference visibleCoordinate = "Aristotle MCGS observer surface"
    calibrationReference dependencyCoordinate = "ResidualObserverDependencyExact"
    calibrationReference provenanceCoordinate = "GovernedObservationProvenanceExact"

    controlReference : ProbeControl → String
    controlReference inspectDependency = "inspect dependency discriminator"
    controlReference inspectProvenance = "inspect provenance discriminator"
    controlReference inspectBoth = "inspect joint merge guard"

------------------------------------------------------------------------
-- 2. History-sensitive fibre: same present proof surface can require different
-- downstream merge choices.
------------------------------------------------------------------------

historySurface : History.HistoryConditionedChoiceSurface
historySurface = record
  { History = Experiment.BranchWorld
  ; Observation = Merge.Surface
  ; Pattern = Merge.DependencyCode × Merge.ProvenanceCode
  ; Choice = Experiment.MergeDecision
  ; observe = Experiment.coarseProofObserver
  ; patternOf = Experiment.guardObserver
  ; choose = Experiment.mergeDecision
  ; historyReading =
      "Aristotle branch history: present proof surface does not determine hidden dependency/provenance or the merge decision."
  }

leftWorldDistinctFromHiddenDependencyWorld :
  Experiment.leftWorld ≡ Experiment.hiddenDependencyWorld → ⊥
leftWorldDistinctFromHiddenDependencyWorld ()

historySensitiveMergeWitness :
  History.DistinctHistoriesSameObservationDifferentChoice historySurface
historySensitiveMergeWitness = record
  { leftHistory = Experiment.leftWorld
  ; rightHistory = Experiment.hiddenDependencyWorld
  ; historiesDistinct = leftWorldDistinctFromHiddenDependencyWorld
  ; samePresentObservation = refl
  ; choicesDiffer = λ ()
  }

------------------------------------------------------------------------
-- 3. One search iteration is explicitly staged.
------------------------------------------------------------------------

data LoopStage : Set where
  liveHypotheses
  collisionLocated
  discriminatorSynthesised
  experimentObserved
  fibreRefined
  discoveriesMerged
  certificatesReopened
  consumerClosed
  : LoopStage

record SearchIteration : Set₁ where
  constructor searchIteration
  field
    stage : LoopStage
    live : Experiment.BranchWorld → Set
    consumer : Experiment.BranchWorld → Experiment.MergeDecision
    stageReference : String

open SearchIteration public

initialIteration : SearchIteration
initialIteration =
  searchIteration
    liveHypotheses
    Experiment.allBranchesLive
    Experiment.mergeDecision
    "all finite Aristotle branch worlds initially live"

record CollisionReceipt (iteration : SearchIteration) : Set₁ where
  constructor collisionReceipt
  field
    collision :
      Consumer.ConsumerRelevantCollision
        Experiment.coarseProofObserver
        (consumer iteration)
    collisionReference : String

open CollisionReceipt public

initialCollision : CollisionReceipt initialIteration
initialCollision =
  collisionReceipt
    Experiment.dependencyMergeCollision
    "same visible proof state, different dependency, different merge decision"

record DiscriminatorReceipt (iteration : SearchIteration) : Set₁ where
  constructor discriminatorReceipt
  field
    bundle : Synthesis.ExperimentBundle Experiment.BranchWorld
    collision : CollisionReceipt iteration
    separates :
      Synthesis.BundleSeparates
        bundle
        (Consumer.left (CollisionReceipt.collision collision))
        (Consumer.right (CollisionReceipt.collision collision))
    synthesisReference : String

open DiscriminatorReceipt public

initialDependencyDiscriminator : DiscriminatorReceipt initialIteration
initialDependencyDiscriminator =
  discriminatorReceipt
    Experiment.dependencyProbe
    initialCollision
    Experiment.dependencyProbeSeparatesHiddenDependencyCollision
    "consumer-relevant dependency collision selects the dependency probe"

record ObservationReceipt
    (iteration : SearchIteration)
    (discriminator : DiscriminatorReceipt iteration) : Set₁ where
  constructor observationReceipt
  field
    outcome : Synthesis.Observation (bundle discriminator)
    possible :
      Planner.OutcomePossible
        (live iteration)
        (bundle discriminator)
        outcome
    observationReference : String

open ObservationReceipt public

localDependencyOutcomePossible :
  Planner.OutcomePossible
    Experiment.allBranchesLive
    Experiment.dependencyProbe
    Merge.localDependency
localDependencyOutcomePossible =
  Experiment.leftWorld , (tt , refl)

initialObservation :
  ObservationReceipt initialIteration initialDependencyDiscriminator
initialObservation =
  observationReceipt
    Merge.localDependency
    localDependencyOutcomePossible
    "dependency probe observed the local-dependency branch"

refinedAfter :
  ∀ {iteration discriminator} →
  ObservationReceipt iteration discriminator →
  Experiment.BranchWorld → Set
refinedAfter {iteration} {discriminator} observation =
  Planner.RefineByBundle
    (live iteration)
    (bundle discriminator)
    (outcome observation)

record RefinementReceipt
    (iteration : SearchIteration)
    (discriminator : DiscriminatorReceipt iteration)
    (observation : ObservationReceipt iteration discriminator) : Set₁ where
  constructor refinementReceipt
  field
    refinedLive : Experiment.BranchWorld → Set
    exactRefinement :
      ∀ world →
      refinedLive world →
      refinedAfter observation world
    refinementReference : String

open RefinementReceipt public

initialRefinement :
  RefinementReceipt initialIteration initialDependencyDiscriminator initialObservation
initialRefinement =
  refinementReceipt
    (refinedAfter initialObservation)
    (λ world evidence → evidence)
    "live branch fibre intersected with the realised dependency outcome"

------------------------------------------------------------------------
-- 4. Compatible discoveries merge only with both the merge guard and the
-- independent least-privilege admission receipt.
------------------------------------------------------------------------

canonicalAdmittedMerge :
  Governance.AdmittedGuardedMerge Merge.leftBranch Merge.compatibleRightBranch
canonicalAdmittedMerge = Governance.canonicalAdmittedCompatibleMerge

------------------------------------------------------------------------
-- 5. Selective reopening is exact reverse dependency closure.
------------------------------------------------------------------------

data Artifact : Set where
  dependencyCertificate
  mergeCertificate
  consumerCertificate
  unrelatedCertificate
  : Artifact

data Depends : Artifact → Artifact → Set where
  dependencyAffectsMerge : Depends dependencyCertificate mergeCertificate
  mergeAffectsConsumer : Depends mergeCertificate consumerCertificate

changedDependencyReopensMerge :
  Affected.ReopeningObligation Depends dependencyCertificate mergeCertificate
changedDependencyReopensMerge =
  Affected.oneEdgeCreatesReopeningObligation dependencyAffectsMerge

mergeReopensConsumer :
  Affected.ReopeningObligation Depends mergeCertificate consumerCertificate
mergeReopensConsumer =
  Affected.oneEdgeCreatesReopeningObligation mergeAffectsConsumer

changedDependencyReopensConsumer :
  Affected.ReopeningObligation Depends dependencyCertificate consumerCertificate
changedDependencyReopensConsumer =
  Affected.obligationsCompose changedDependencyReopensMerge mergeReopensConsumer

selectiveConsumerReopening :
  Adaptive.SelectiveCertificateReopening Artifact Depends dependencyCertificate
selectiveConsumerReopening =
  Adaptive.selectiveCertificateReopening
    consumerCertificate
    (Affected.dependencyPath changedDependencyReopensConsumer)
    "dependency observation changed; reopen downstream merge and consumer certificate through exact affected closure"

------------------------------------------------------------------------
-- 6. Loop continuation versus closure.
------------------------------------------------------------------------

continuationPlan :
  Planner.SequentialConsumerPlan
    Experiment.mergeDecision
    Experiment.allBranchesLive
continuationPlan = Experiment.dependencyThenProvenancePlan

ConsumerClosedOn : (Experiment.BranchWorld → Set) → Set
ConsumerClosedOn live =
  ∀ left right →
  live left → live right →
  Experiment.mergeDecision left ≡ Experiment.mergeDecision right

closeWhenConsumerConstant :
  ∀ {live} →
  ConsumerClosedOn live →
  Planner.SequentialConsumerPlan Experiment.mergeDecision live
closeWhenConsumerConstant = Planner.closeConsumer

------------------------------------------------------------------------
-- 7. Capstone receipt: all canonical owners appear as obligations of one loop.
------------------------------------------------------------------------

record ActiveExperimentalProofSearchLoop : Set₂ where
  constructor activeExperimentalProofSearchLoop
  field
    coordinateDesign :
      Coordinate.ExperimentalCoordinateDesign
        Experiment.BranchWorld ProbeControl CoordinateValue CoordinateDimension
    initial : SearchIteration
    collision : CollisionReceipt initial
    discriminator : DiscriminatorReceipt initial
    observation : ObservationReceipt initial discriminator
    refinement : RefinementReceipt initial discriminator observation
    admittedMerge :
      Governance.AdmittedGuardedMerge Merge.leftBranch Merge.compatibleRightBranch
    reopening :
      Adaptive.SelectiveCertificateReopening Artifact Depends dependencyCertificate
    adaptiveContinuation :
      Planner.SequentialConsumerPlan
        Experiment.mergeDecision
        Experiment.allBranchesLive
    historySensitiveChoice :
      History.DistinctHistoriesSameObservationDifferentChoice historySurface
    loopReference : String

open ActiveExperimentalProofSearchLoop public

canonicalActiveExperimentalProofSearchLoop : ActiveExperimentalProofSearchLoop
canonicalActiveExperimentalProofSearchLoop =
  activeExperimentalProofSearchLoop
    proofSearchCoordinateDesign
    initialIteration
    initialCollision
    initialDependencyDiscriminator
    initialObservation
    initialRefinement
    canonicalAdmittedMerge
    selectiveConsumerReopening
    continuationPlan
    historySensitiveMergeWitness
    "consumer-indexed active experimental proof search over Aristotle MCGS: locate a visible-state collision, acquire only the discriminator needed by the merge consumer, refine the branch fibre, merge compatible proved discoveries under provenance and least-privilege guards, reopen exactly affected downstream certificates, and continue adaptively until the consumer closes"

------------------------------------------------------------------------
-- 8. Boundary.
------------------------------------------------------------------------

record ActiveExperimentalProofSearchBoundary : Set where
  constructor activeExperimentalProofSearchBoundary
  field
    proofSearchMustIdentifyCompleteHiddenStateBeforeClosing : Bool
    proofSearchMustIdentifyCompleteHiddenStateBeforeClosingIsFalse :
      proofSearchMustIdentifyCompleteHiddenStateBeforeClosing ≡ false

    visibleProofStateDeterminesHistorySensitiveMergeChoice : Bool
    visibleProofStateDeterminesHistorySensitiveMergeChoiceIsFalse :
      visibleProofStateDeterminesHistorySensitiveMergeChoice ≡ false

    everyNewObservationReopensEveryCertificate : Bool
    everyNewObservationReopensEveryCertificateIsFalse :
      everyNewObservationReopensEveryCertificate ≡ false

    compatibleKnowledgeJoinBypassesLeastPrivilegeAdmission : Bool
    compatibleKnowledgeJoinBypassesLeastPrivilegeAdmissionIsFalse :
      compatibleKnowledgeJoinBypassesLeastPrivilegeAdmission ≡ false

    nextDiscriminatorMayDependOnPreviousOutcome : Bool
    nextDiscriminatorMayDependOnPreviousOutcomeIsTrue :
      nextDiscriminatorMayDependOnPreviousOutcome ≡ true

    activeExperimentalLoopIsClaimedByAristotlePaper : Bool
    activeExperimentalLoopIsClaimedByAristotlePaperIsFalse :
      activeExperimentalLoopIsClaimedByAristotlePaper ≡ false

canonicalActiveExperimentalProofSearchBoundary : ActiveExperimentalProofSearchBoundary
canonicalActiveExperimentalProofSearchBoundary =
  activeExperimentalProofSearchBoundary
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
