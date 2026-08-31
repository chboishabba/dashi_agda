module DASHI.Reasoning.AristotleActiveExperimentalProofSearchDynamicsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Reasoning.AristotleMergeExperimentDesignExact as Experiment
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Loop

------------------------------------------------------------------------
-- EXPLICIT DYNAMICS FOR THE ACTIVE EXPERIMENTAL PROOF-SEARCH LOOP
--
-- The capstone owner packages the proof obligations carried by one iteration.
-- This sibling owner makes the control-flow itself first-class, including the
-- reopening -> next-live-iteration edge and the alternative early closure edge.
------------------------------------------------------------------------

data LoopTransition : Loop.LoopStage → Loop.LoopStage → Set where
  locateConsumerCollision :
    LoopTransition Loop.liveHypotheses Loop.collisionLocated
  synthesiseDiscriminator :
    LoopTransition Loop.collisionLocated Loop.discriminatorSynthesised
  runInformationExperiment :
    LoopTransition Loop.discriminatorSynthesised Loop.experimentObserved
  refineLiveFibre :
    LoopTransition Loop.experimentObserved Loop.fibreRefined
  mergeCompatibleDiscoveries :
    LoopTransition Loop.fibreRefined Loop.discoveriesMerged
  reopenAffectedCertificates :
    LoopTransition Loop.discoveriesMerged Loop.certificatesReopened
  iterateAfterReopening :
    LoopTransition Loop.certificatesReopened Loop.liveHypotheses
  closeConsumerFromRefinedFibre :
    LoopTransition Loop.fibreRefined Loop.consumerClosed

data LoopPath : Loop.LoopStage → Loop.LoopStage → Set where
  pathRefl : ∀ {stage} → LoopPath stage stage
  pathStep :
    ∀ {start middle finish} →
    LoopTransition start middle →
    LoopPath middle finish →
    LoopPath start finish

appendPath :
  ∀ {start middle finish} →
  LoopPath start middle →
  LoopPath middle finish →
  LoopPath start finish
appendPath pathRefl right = right
appendPath (pathStep transition rest) right =
  pathStep transition (appendPath rest right)

canonicalOneIterationCycle :
  LoopPath Loop.liveHypotheses Loop.liveHypotheses
canonicalOneIterationCycle =
  pathStep locateConsumerCollision
    (pathStep synthesiseDiscriminator
      (pathStep runInformationExperiment
        (pathStep refineLiveFibre
          (pathStep mergeCompatibleDiscoveries
            (pathStep reopenAffectedCertificates
              (pathStep iterateAfterReopening pathRefl))))))

canonicalClosurePath :
  LoopPath Loop.liveHypotheses Loop.consumerClosed
canonicalClosurePath =
  pathStep locateConsumerCollision
    (pathStep synthesiseDiscriminator
      (pathStep runInformationExperiment
        (pathStep refineLiveFibre
          (pathStep closeConsumerFromRefinedFibre pathRefl))))

------------------------------------------------------------------------
-- Closure remains consumer-relative: once a live fibre makes the merge
-- consumer constant, the canonical sequential planner supplies a terminal plan.
------------------------------------------------------------------------

consumerClosureProducesTerminalPlan :
  ∀ {live : Experiment.BranchWorld → Set} →
  Loop.ConsumerClosedOn live →
  Planner.SequentialConsumerPlan Experiment.mergeDecision live
consumerClosureProducesTerminalPlan = Loop.closeWhenConsumerConstant

------------------------------------------------------------------------
-- Reopening is not rollback to the original epistemic state.  It returns the
-- control-flow to a live-search stage after dependency-affected certificates
-- have been marked for reconsideration; the next discriminator can therefore
-- be selected from the updated live fibre.
------------------------------------------------------------------------

record ActiveSearchDynamicsReceipt : Set where
  constructor activeSearchDynamicsReceipt
  field
    oneIterationCanCycle :
      LoopPath Loop.liveHypotheses Loop.liveHypotheses
    refinedFibreCanCloseDirectly :
      LoopPath Loop.liveHypotheses Loop.consumerClosed
    adaptivePlan :
      Planner.SequentialConsumerPlan
        Experiment.mergeDecision
        Experiment.allBranchesLive
    dynamicsReference : String

canonicalActiveSearchDynamicsReceipt : ActiveSearchDynamicsReceipt
canonicalActiveSearchDynamicsReceipt =
  activeSearchDynamicsReceipt
    canonicalOneIterationCycle
    canonicalClosurePath
    Loop.continuationPlan
    "active proof search has an explicit iterate-or-close control flow: collision -> discriminator -> experiment -> refinement, then either guarded merge -> selective reopening -> new live iteration, or consumer-relative closure"

record ActiveSearchDynamicsBoundary : Set where
  constructor activeSearchDynamicsBoundary
  field
    reopeningMeansAllPreviousKnowledgeWasDiscarded : Bool
    reopeningMeansAllPreviousKnowledgeWasDiscardedIsFalse :
      reopeningMeansAllPreviousKnowledgeWasDiscarded ≡ false

    everyIterationMustMergeBeforeClosing : Bool
    everyIterationMustMergeBeforeClosingIsFalse :
      everyIterationMustMergeBeforeClosing ≡ false

    refinedConsumerClosureCanTerminateSearch : Bool
    refinedConsumerClosureCanTerminateSearchIsTrue :
      refinedConsumerClosureCanTerminateSearch ≡ true

    reopenedSearchMaySelectAnotherOutcomeDependentProbe : Bool
    reopenedSearchMaySelectAnotherOutcomeDependentProbeIsTrue :
      reopenedSearchMaySelectAnotherOutcomeDependentProbe ≡ true

canonicalActiveSearchDynamicsBoundary : ActiveSearchDynamicsBoundary
canonicalActiveSearchDynamicsBoundary =
  activeSearchDynamicsBoundary
    false refl
    false refl
    true refl
    true refl
