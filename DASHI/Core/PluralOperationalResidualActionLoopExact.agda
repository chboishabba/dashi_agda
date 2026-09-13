module DASHI.Core.PluralOperationalResidualActionLoopExact where

------------------------------------------------------------------------
-- PLURAL OPERATIONAL RESIDUAL-ACTION LOOP
--
-- Open operational-justice coordinates are not terminal labels.  They route to
-- evidence/action producers; new braided observations can revise the residual
-- and therefore the next action.  Salience remains consumer- and authority-
-- relative rather than being inferred from residual class alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PluralEpistemicOperationalClosureExact as Operational
import DASHI.Core.PluralOperationalEvidenceBraidBidiExact as Braid
import DASHI.Core.ResidualActionAdaptiveLoopExact as Adaptive
import DASHI.Core.ResidualActionSalienceExact as Salience
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision

------------------------------------------------------------------------
-- Operational residual and action carriers.
------------------------------------------------------------------------

data OperationalResidual : Set where
  realisedEffectResidual
  communityOutcomeResidual
  communityAuthorityResidual
  monitoringResidual
  correctionResponseResidual
  recurrencePreventionResidual
  : OperationalResidual

data OperationalAction : Set where
  obtainAffectedCommunityOutcome
  obtainAuthorityBearingCommunityReceipt
  obtainIndependentMonitoring
  testCorrectionResponsiveness
  observeRecurrencePrevention
  holdAndReassess
  : OperationalAction

data OperationalActionAuthority : Set where
  communityAuthorized
  independentMonitorAuthorized
  institutionalActionAuthorized
  authorityUnresolved
  : OperationalActionAuthority

residualFor : Operational.OperationalClosureCoordinate → OperationalResidual
residualFor Operational.declaredCommitmentCoordinate = realisedEffectResidual
residualFor Operational.realisedEffectCoordinate = realisedEffectResidual
residualFor Operational.communityDefinedOutcomeCoordinate = communityOutcomeResidual
residualFor Operational.communityAuthorityCoordinate = communityAuthorityResidual
residualFor Operational.independentMonitoringCoordinate = monitoringResidual
residualFor Operational.correctionResponseCoordinate = correctionResponseResidual
residualFor Operational.preventionOfRecurrenceCoordinate = recurrencePreventionResidual

defaultActionFor : OperationalResidual → OperationalAction
defaultActionFor realisedEffectResidual = obtainAffectedCommunityOutcome
defaultActionFor communityOutcomeResidual = obtainAffectedCommunityOutcome
defaultActionFor communityAuthorityResidual = obtainAuthorityBearingCommunityReceipt
defaultActionFor monitoringResidual = obtainIndependentMonitoring
defaultActionFor correctionResponseResidual = testCorrectionResponsiveness
defaultActionFor recurrencePreventionResidual = observeRecurrencePrevention

------------------------------------------------------------------------
-- Action admission is separate from salience/need.
------------------------------------------------------------------------

record OperationalActionPlan : Set where
  constructor operational-action-plan
  field
    residual : OperationalResidual
    selectedAction : OperationalAction
    authority : OperationalActionAuthority
    consumerReference : String
    evidenceStrandReference : String
    actionBasis : String
    salienceReference : String
    actionNeeded : Bool
    actionNeededIsTrue : actionNeeded ≡ true
    highSalienceCreatesAuthority : Bool
    highSalienceCreatesAuthorityIsFalse : highSalienceCreatesAuthority ≡ false

open OperationalActionPlan public

communityOutcomePlan : OperationalActionPlan
communityOutcomePlan = operational-action-plan
  communityOutcomeResidual
  obtainAffectedCommunityOutcome
  communityAuthorized
  "consumer requiring realised Country/community outcome"
  "affected-community outcome strand"
  "an institutional success report cannot factor the affected-community outcome"
  "consumer-critical until community-defined outcome coordinate is paid"
  true refl false refl

communityAuthorityPlan : OperationalActionPlan
communityAuthorityPlan = operational-action-plan
  communityAuthorityResidual
  obtainAuthorityBearingCommunityReceipt
  communityAuthorized
  "consumer requiring authority-bearing community participation"
  "affected-community authority strand"
  "consultation/content receipt does not transfer or recover community authority"
  "action-critical because operational closure requires the authority coordinate"
  true refl false refl

correctionResponsePlan : OperationalActionPlan
correctionResponsePlan = operational-action-plan
  correctionResponseResidual
  testCorrectionResponsiveness
  institutionalActionAuthorized
  "consumer requiring a correction loop that changes realised operation"
  "community feedback crossed with institutional correction-response strand"
  "feedback recorded is not the same outcome as feedback changing operation"
  "action-critical where correction response remains open"
  true refl false refl

------------------------------------------------------------------------
-- Evidence/action loops remain revision-capable.
------------------------------------------------------------------------

record OperationalPostActionObservation : Set where
  constructor operational-post-action-observation
  field
    action : OperationalAction
    strandReference : String
    observationReference : String
    provenanceReference : String
    authorityReference : String
    previousResidual : OperationalResidual
    revisedResidual : OperationalResidual
    conclusionMayChange : Bool
    conclusionMayChangeIsTrue : conclusionMayChange ≡ true

open OperationalPostActionObservation public

communityOutcomeReopensCorrection : OperationalPostActionObservation
communityOutcomeReopensCorrection = operational-post-action-observation
  obtainAffectedCommunityOutcome
  "affected-community outcome strand"
  "later community outcome shows declared activity did not yet alter realised relation"
  "community evidence provenance retained"
  "community authority remains strand-local"
  communityOutcomeResidual
  correctionResponseResidual
  true refl

------------------------------------------------------------------------
-- Imported generic adaptive/revision boundaries.
------------------------------------------------------------------------

adaptiveBoundary : Adaptive.ResidualActionAdaptiveLoopBoundary
adaptiveBoundary = Adaptive.canonicalResidualActionAdaptiveLoopBoundary

newObservationMayChangeResidual :
  Adaptive.newObservationMayChangeResidualClass adaptiveBoundary ≡ true
newObservationMayChangeResidual = refl

updatedResidualMayChangeNextExperiment :
  Adaptive.updatedResidualMaySelectDifferentNextExperiment adaptiveBoundary ≡ true
updatedResidualMayChangeNextExperiment = refl

appendOnlyEvidenceNeedNotMakeActionMonotone :
  Adaptive.appendOnlyEvidenceNeedNotMakeActionMonotone adaptiveBoundary ≡ true
appendOnlyEvidenceNeedNotMakeActionMonotone = refl

salienceBoundary : Salience.ResidualActionSalienceBoundary
salienceBoundary = Salience.canonicalResidualActionSalienceBoundary

highSalienceDoesNotCreateActionAuthority :
  Salience.highSalienceCreatesActionAuthority salienceBoundary ≡ false
highSalienceDoesNotCreateActionAuthority = refl

sameResidualNeedNotRequireSameActionAcrossConsumers :
  Salience.sameResidualRequiresSameActionAcrossConsumers salienceBoundary ≡ false
sameResidualNeedNotRequireSameActionAcrossConsumers = refl

revisionBoundary : Revision.AppendOnlyEvidenceRevisionBoundary
revisionBoundary = Revision.canonicalAppendOnlyEvidenceRevisionBoundary

earlierEvidenceNeedNotBeDeletedForRevision :
  Revision.earlierEvidenceMustBeDeletedBeforeConclusionRevision revisionBoundary ≡ false
earlierEvidenceNeedNotBeDeletedForRevision = refl

------------------------------------------------------------------------
-- Braided evidence routing.
------------------------------------------------------------------------

communityOutcomeUsesCommunityStrand :
  Braid.evidenceStrand Braid.communityOutcomePaymentCandidate
  ≡ Braid.affectedCommunityOutcomeStrand
communityOutcomeUsesCommunityStrand = refl

correctionUsesCorrectionResponseStrand :
  Braid.evidenceStrand Braid.correctionPaymentCandidate
  ≡ Braid.correctionResponseStrand
correctionUsesCorrectionResponseStrand = refl

paymentDoesNotTransferAuthority :
  Braid.paymentAutomaticallyTransfersAuthority Braid.communityOutcomePaymentCandidate ≡ false
paymentDoesNotTransferAuthority = refl

------------------------------------------------------------------------
-- First-open routing for a generic snapshot.
------------------------------------------------------------------------

data OperationalNextStep : Set where
  noFurtherActionForThisConsumer
  actOnRealisedEffect
  actOnCommunityOutcome
  actOnCommunityAuthority
  actOnMonitoring
  actOnCorrection
  actOnPrevention
  : OperationalNextStep

firstOpen : Operational.OperationalClosureSnapshot → OperationalNextStep
firstOpen snapshot with Operational.stateFor snapshot Operational.realisedEffectCoordinate
... | Operational.coordinateOpen = actOnRealisedEffect
... | Operational.coordinateSourceUnresolved = actOnRealisedEffect
... | _ with Operational.stateFor snapshot Operational.communityDefinedOutcomeCoordinate
...   | Operational.coordinateOpen = actOnCommunityOutcome
...   | Operational.coordinateSourceUnresolved = actOnCommunityOutcome
...   | _ with Operational.stateFor snapshot Operational.communityAuthorityCoordinate
...     | Operational.coordinateOpen = actOnCommunityAuthority
...     | Operational.coordinateSourceUnresolved = actOnCommunityAuthority
...     | _ with Operational.stateFor snapshot Operational.independentMonitoringCoordinate
...       | Operational.coordinateOpen = actOnMonitoring
...       | Operational.coordinateSourceUnresolved = actOnMonitoring
...       | _ with Operational.stateFor snapshot Operational.correctionResponseCoordinate
...         | Operational.coordinateOpen = actOnCorrection
...         | Operational.coordinateSourceUnresolved = actOnCorrection
...         | _ with Operational.stateFor snapshot Operational.preventionOfRecurrenceCoordinate
...           | Operational.coordinateOpen = actOnPrevention
...           | Operational.coordinateSourceUnresolved = actOnPrevention
...           | _ = noFurtherActionForThisConsumer

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data SalienceEqualsAuthority : Set where
data OneCommunityObservationClosesEveryCoordinate : Set where
data StateActionAdmissionClosesCommunityOutcome : Set where
data NewEvidenceCanOnlyStrengthenPriorConclusion : Set where
data EvidenceCrossingFusesAuthority : Set where

salienceDoesNotEqualAuthority : SalienceEqualsAuthority → ⊥
salienceDoesNotEqualAuthority ()

oneCommunityObservationDoesNotCloseEveryCoordinate :
  OneCommunityObservationClosesEveryCoordinate → ⊥
oneCommunityObservationDoesNotCloseEveryCoordinate ()

stateActionAdmissionDoesNotCloseCommunityOutcome :
  StateActionAdmissionClosesCommunityOutcome → ⊥
stateActionAdmissionDoesNotCloseCommunityOutcome ()

newEvidenceNeedNotOnlyStrengthenPriorConclusion :
  NewEvidenceCanOnlyStrengthenPriorConclusion → ⊥
newEvidenceNeedNotOnlyStrengthenPriorConclusion ()

evidenceCrossingDoesNotFuseAuthority : EvidenceCrossingFusesAuthority → ⊥
evidenceCrossingDoesNotFuseAuthority ()
