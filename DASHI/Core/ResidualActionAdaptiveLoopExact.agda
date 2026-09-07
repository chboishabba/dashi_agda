module DASHI.Core.ResidualActionAdaptiveLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.MechanismModelDiscriminationExact as Model
import DASHI.Core.ResidualActionPolicyExact as Action
import DASHI.Core.AdaptiveConsumerModelLoopExact as ConsumerLoop
import DASHI.Core.AdaptiveMechanismDiscriminationPlannerExact as Planner
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision
import DASHI.Core.ResidualActionSalienceExact as Salience

------------------------------------------------------------------------
-- ADAPTIVE RESIDUAL-ACTION FEEDBACK LOOP
--
-- The action layer is not terminal.  A measurement, perturbation, hold,
-- reopening, acceptance or refutation changes what must be observed next.
-- Evidence history may be append-only while residual/action conclusions remain
-- non-monotone, and the salience of a residual remains consumer-relative.
------------------------------------------------------------------------

data ActionOutcomeClass : Set where
  noExecution
  observationProduced
  perturbationApplied
  consumerClosed
  modelRefuted
  inconclusiveOutcome
  : ActionOutcomeClass

record PostActionObservation : Set where
  constructor postActionObservation
  field
    actionKind : Action.ResidualActionKind
    outcomeClass : ActionOutcomeClass
    observationReference : String
    sameObjectContextReference : String
    protocolOrExecutionReference : String
    provenanceReference : String

open PostActionObservation public

record ResidualUpdate : Set where
  constructor residualUpdate
  field
    before : Model.ModelResidual
    actionKind : Action.ResidualActionKind
    observation : PostActionObservation
    after : Model.ModelResidual
    updateReference : String
    residualRecalculationReference : String

open ResidualUpdate public

record AdaptiveResidualCycle : Set₁ where
  constructor adaptiveResidualCycle
  field
    semantics : Action.ResidualActionSemantics
    beforeResidual : Model.ModelResidual
    selectedKind : Action.ResidualActionKind
    selectedAction : Action.AdmissibleResidualAction semantics beforeResidual selectedKind
    postActionObservation : PostActionObservation
    residualUpdate : ResidualUpdate
    nextStepReference : String
    consumerReference : String
    stoppingRuleReference : String

open AdaptiveResidualCycle public

record ResidualActionEvidenceWeld : Set₁ where
  constructor residualActionEvidenceWeld
  field
    Evidence : Set
    evidenceUpdate : ConsumerLoop.EvidenceUpdate Evidence
    residualUpdate : ResidualUpdate
    observationAssimilationReference : String
    selectiveReopeningReference : String

open ResidualActionEvidenceWeld public

record ResidualConditionedContinuation : Set₂ where
  constructor residualConditionedContinuation
  field
    problem : Planner.AdaptiveDiscriminationProblem
    policy : Planner.ResidualConditionedExperimentPolicy problem
    latestResidual : Model.ModelResidual
    continuationReference : String

open ResidualConditionedContinuation public

------------------------------------------------------------------------
-- Explicit BIDI seam: the loop consumes the append-only-history and salience
-- boundaries rather than silently assuming confidence/action monotonicity.
------------------------------------------------------------------------

existingAppendOnlyRevisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
existingAppendOnlyRevisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

existingResidualSalienceBoundary : Salience.ResidualActionSalienceBoundary
existingResidualSalienceBoundary = Salience.canonicalResidualActionSalienceBoundary

record ResidualActionAdaptiveLoopBoundary : Set where
  constructor residualActionAdaptiveLoopBoundary
  field
    admittedActionAutomaticallyClosesLoop : Bool
    admittedActionAutomaticallyClosesLoopIsFalse :
      admittedActionAutomaticallyClosesLoop ≡ false

    perturbationWithoutPostObservationProvesCausality : Bool
    perturbationWithoutPostObservationProvesCausalityIsFalse :
      perturbationWithoutPostObservationProvesCausality ≡ false

    newObservationMayChangeResidualClass : Bool
    newObservationMayChangeResidualClassIsTrue :
      newObservationMayChangeResidualClass ≡ true

    updatedResidualMaySelectDifferentNextExperiment : Bool
    updatedResidualMaySelectDifferentNextExperimentIsTrue :
      updatedResidualMaySelectDifferentNextExperiment ≡ true

    consumerClosureMayTerminateBeforeMechanismIdentity : Bool
    consumerClosureMayTerminateBeforeMechanismIdentityIsTrue :
      consumerClosureMayTerminateBeforeMechanismIdentity ≡ true

    evidenceUpdateNeedNotReopenUnrelatedCarriers : Bool
    evidenceUpdateNeedNotReopenUnrelatedCarriersIsTrue :
      evidenceUpdateNeedNotReopenUnrelatedCarriers ≡ true

    appendOnlyEvidenceNeedNotMakeActionMonotone : Bool
    appendOnlyEvidenceNeedNotMakeActionMonotoneIsTrue :
      appendOnlyEvidenceNeedNotMakeActionMonotone ≡ true

    residualSalienceMayChangeWithConsumer : Bool
    residualSalienceMayChangeWithConsumerIsTrue :
      residualSalienceMayChangeWithConsumer ≡ true

canonicalResidualActionAdaptiveLoopBoundary : ResidualActionAdaptiveLoopBoundary
canonicalResidualActionAdaptiveLoopBoundary =
  residualActionAdaptiveLoopBoundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
