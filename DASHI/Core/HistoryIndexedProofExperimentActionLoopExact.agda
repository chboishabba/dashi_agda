module DASHI.Core.HistoryIndexedProofExperimentActionLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Core.SequentialRelationalExperimentPlannerExact as Experiment
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Core.ProofCarryingPhysicalExecutionBoundaryExact as Physical
import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Reasoning.HistoryTimeIndexedAlgorithmModelExact as Model

------------------------------------------------------------------------
-- HISTORY-INDEXED PROOF / EXPERIMENT / ACTION CYBERNETIC LOOP
--
-- A single live residual fibre may be advanced by four qualitatively different
-- moves: internal proof search, information acquisition, physical experiment,
-- or admitted physical action.  This module deliberately does not identify
-- those moves.  It records the common OODA-shaped control spine while keeping
-- their authority and evidence obligations distinct.
------------------------------------------------------------------------

data EpistemicMoveKind : Set where
  thinkMove
  lookMove
  testMove
  actMove
  : EpistemicMoveKind

data OODAPhase : Set where
  observePhase
  orientPhase
  decidePhase
  actPhase
  feedbackPhase
  : OODAPhase

data MoveOutcome : Set where
  refined
  closedForConsumer
  physicallyExecuted
  unresolved
  rejected
  : MoveOutcome

record LiveResidualFibre : Set₁ where
  constructor live-residual-fibre
  field
    Hypothesis : Set
    live : Hypothesis → Set
    residualReference : String
    consumerReference : String

open LiveResidualFibre public

record OODAPoint : Set₁ where
  constructor ooda-point
  field
    phase : OODAPhase
    historyReference : String
    timeReference : String
    modelReference : String
    stateReference : String
    residualReferenceAtPoint : String

open OODAPoint public

record CandidateMove (fibre : LiveResidualFibre) : Set₁ where
  constructor candidate-move
  field
    kind : EpistemicMoveKind
    sourceResidual : residualReference fibre ≡ residualReference fibre
    candidateReference : String
    expectedConsumerGainReference : String
    costReference : String

open CandidateMove public

------------------------------------------------------------------------
-- Proof search is admitted by least privilege before it can become a live
-- route.  A theorem name, analogy, or conjecture cannot silently close a leaf.
------------------------------------------------------------------------

record ProofMoveReceipt (fibre : LiveResidualFibre) : Set where
  constructor proof-move-receipt
  field
    candidate : CandidateMove fibre
    isProofMove : kind candidate ≡ thinkMove
    admission : ProofSearch.RouteAdmission
    liveRoute : ProofSearch.LiveProofSearch
    routeExact : liveRoute ≡ ProofSearch.elaborateRoute admission
    proofReference : String

open ProofMoveReceipt public

------------------------------------------------------------------------
-- Experiments refine a live hypothesis fibre by a relation between hypothesis,
-- experiment, and observed outcome.  They need not reveal full theory identity:
-- termination is consumer-relative.
------------------------------------------------------------------------

record RelationalExperimentMoveReceipt
    (Hypothesis Experiment Observation Consumer : Set)
    (system : Experiment.RelationalExperimentSystem Hypothesis Experiment Observation)
    (consumer : Hypothesis → Consumer)
    (live : Hypothesis → Set) : Set₂ where
  constructor relational-experiment-move-receipt
  field
    plan : Experiment.CertifiedSequentialRelationalPlan system consumer live
    selectedExperimentReference : String
    governedObservationReference : String
    refinementReference : String

open RelationalExperimentMoveReceipt public

------------------------------------------------------------------------
-- Physical action remains behind the repository's proof-carrying promotion
-- boundary.  The same candidate being reasoned about must be the one promoted;
-- no generic candidate -> execution coercion is exposed here.
------------------------------------------------------------------------

record PhysicalActionMoveReceipt (fibre : LiveResidualFibre) : Set₁ where
  constructor physical-action-move-receipt
  field
    candidate : CandidateMove fibre
    isActionMove : kind candidate ≡ actMove
    admissibilityReference : String
    authorityReference : String
    physicalPromotionReference : String
    literalActionReference : String
    resultingStateReference : String
    depositedResidualReference : String

open PhysicalActionMoveReceipt public

------------------------------------------------------------------------
-- One step on the live residual spine.  The state of ignorance after the step
-- is first-class, so success, execution, and epistemic closure remain distinct.
------------------------------------------------------------------------

record CyberneticStep : Set₁ where
  constructor cybernetic-step
  field
    before : LiveResidualFibre
    move : CandidateMove before
    after : LiveResidualFibre
    outcome : MoveOutcome
    observationReference : String
    orientationReference : String
    decisionReference : String
    actionReference : String
    feedbackReference : String
    sameSpineReference : String

open CyberneticStep public

record ConsumerClosedAt (fibre : LiveResidualFibre) : Set₁ where
  constructor consumer-closed-at
  field
    Consumer : Set
    consumer : Hypothesis fibre → Consumer
    constantOnLive :
      ∀ left right →
      live fibre left →
      live fibre right →
      consumer left ≡ consumer right
    closureReference : String

open ConsumerClosedAt public

------------------------------------------------------------------------
-- Branching controller: if the requested consumer is not yet constant on the
-- live fibre, the system may choose another admitted epistemic move.  This is
-- the common typed seam for 'think, look, test, or act'.
------------------------------------------------------------------------

data NextControlDecision (fibre : LiveResidualFibre) : Set₁ where
  closeNow : ConsumerClosedAt fibre → NextControlDecision fibre
  continueWith : CandidateMove fibre → NextControlDecision fibre

record HistoryIndexedCyberneticLoop : Set₂ where
  constructor history-indexed-cybernetic-loop
  field
    ModelSurface : Model.HistoryTimeAlgorithmModelSurface
    initialResidual : LiveResidualFibre
    next : (fibre : LiveResidualFibre) → NextControlDecision fibre
    step :
      (fibre : LiveResidualFibre) →
      (candidate : CandidateMove fibre) →
      CyberneticStep
    modelRevisionNeedsAuthority : String
    trajectoryResidueReference : String
    loopReference : String

open HistoryIndexedCyberneticLoop public

------------------------------------------------------------------------
-- Hard boundaries.  These are the control invariants required by the larger
-- operational architecture.
------------------------------------------------------------------------

record ProofExperimentActionLoopBoundary : Set where
  constructor proof-experiment-action-loop-boundary
  field
    proofSearchIsPhysicalExecution : Bool
    proofSearchIsPhysicalExecutionIsFalse : proofSearchIsPhysicalExecution ≡ false

    observationAutomaticallyAuthorisesAction : Bool
    observationAutomaticallyAuthorisesActionIsFalse :
      observationAutomaticallyAuthorisesAction ≡ false

    consumerClosureRequiresFullHypothesisIdentity : Bool
    consumerClosureRequiresFullHypothesisIdentityIsFalse :
      consumerClosureRequiresFullHypothesisIdentity ≡ false

    successfulExecutionErasesResidual : Bool
    successfulExecutionErasesResidualIsFalse :
      successfulExecutionErasesResidual ≡ false

    modelRevisionMayRewritePriorEvidencePath : Bool
    modelRevisionMayRewritePriorEvidencePathIsFalse :
      modelRevisionMayRewritePriorEvidencePath ≡ false

canonicalProofExperimentActionLoopBoundary : ProofExperimentActionLoopBoundary
canonicalProofExperimentActionLoopBoundary =
  proof-experiment-action-loop-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
