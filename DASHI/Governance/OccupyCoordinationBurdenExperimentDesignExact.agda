module DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.RobustExperimentInferenceFrontierExact as Robust
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Archive
import DASHI.Governance.OccupyLibraryMeetingDurationEvidenceExact as Duration

------------------------------------------------------------------------
-- OCCUPY COORDINATION-BURDEN EXPERIMENT-DESIGN FRONTIER.
--
-- This owner does not estimate a causal effect. It specializes the repo's
-- generic robustness / experiment-design frontier to the archival governance
-- problem exposed by the meeting-level process panel.
------------------------------------------------------------------------

data OptionalNat : Set where
  unmeasured : OptionalNat
  measured : Nat → OptionalNat

record MeetingMeasurement : Set where
  constructor meetingMeasurement
  field
    meetingLabel : String
    sourceAnchor : String
    observedIncidenceEdges : OptionalNat
    namedParticipantCount : OptionalNat
    distinctIssueCount : OptionalNat
    meetingDurationMinutes : OptionalNat
    mediationMinutes : OptionalNat
    tabledAgendaItemCount : OptionalNat
    explicitDecisionCount : OptionalNat
    processInterruptionCount : OptionalNat
    sourceCompletenessAudit : Bool

open MeetingMeasurement public

data BurdenOutcome : Set where
  totalMeetingDuration mediationTime tabledAgendaItems unresolvedAgendaItems processInterruptions explicitConflictFlag : BurdenOutcome

data RequiredControl : Set where
  participantCountControl issueCountControl meetingTypeControl externalShockControl sourceCompletenessControl repeatedParticipantControl sourceRegimeControl : RequiredControl

record CoordinationBurdenMeasurementRequirements : Set where
  constructor coordinationBurdenMeasurementRequirements
  field
    requiresIncidenceMeasurement requiresMeetingDuration requiresMediationTime requiresTabledItemCount requiresDecisionCount requiresParticipantCountControl requiresIssueCountControl requiresMeetingTypeControl requiresExternalShockControl requiresSourceCompletenessAudit requiresRepeatedParticipantHandling requiresSourceRegimeControl : Bool
open CoordinationBurdenMeasurementRequirements public

canonicalMeasurementRequirements : CoordinationBurdenMeasurementRequirements
canonicalMeasurementRequirements = coordinationBurdenMeasurementRequirements true true true true true true true true true true true true

oct15CurrentMeasurement : MeetingMeasurement
oct15CurrentMeasurement =
  meetingMeasurement "People's Library first formal Working Group meeting 2011-10-15"
    (Duration.sourceURL Duration.oct15FirstFormalMeeting)
    unmeasured unmeasured unmeasured (measured 180) unmeasured unmeasured unmeasured unmeasured false

oct22CurrentMeasurement : MeetingMeasurement
oct22CurrentMeasurement =
  meetingMeasurement "People's Library Working Group 2011-10-22"
    (Duration.sourceURL Duration.oct22Meeting)
    (measured 18) unmeasured unmeasured (measured 155) unmeasured unmeasured unmeasured unmeasured false

nov28CurrentMeasurement : MeetingMeasurement
nov28CurrentMeasurement =
  meetingMeasurement "People's Library Working Group 2011-11-28" Archive.minutesIndexURL
    (measured 7) (measured 19) (measured 5) unmeasured unmeasured unmeasured unmeasured unmeasured false

dec04CurrentMeasurement : MeetingMeasurement
dec04CurrentMeasurement =
  meetingMeasurement "People's Library Working Group 2011-12-04" Archive.minutesIndexURL
    unmeasured unmeasured unmeasured unmeasured unmeasured (measured 10) unmeasured unmeasured false

------------------------------------------------------------------------
-- CURRENT ACQUISITION FRONTIER AFTER CORPUS MATERIALISATION.
--
-- Materialising OccupyFiles and freezing the holdout are paid and therefore
-- removed from the active acquisition queue. Named-person reconstruction is
-- not an objective. The remaining work targets meeting-level observables and
-- documentary/source-regime controls.
------------------------------------------------------------------------

data EvidenceAcquisitionExperiment : Set where
  recoverMoreMeetingDurations : EvidenceAcquisitionExperiment
  recoverMediationDurations : EvidenceAcquisitionExperiment
  countResolvedTabledAndUnresolvedItems : EvidenceAcquisitionExperiment
  auditDocumentaryCompleteness : EvidenceAcquisitionExperiment
  expandSourceRegimeControls : EvidenceAcquisitionExperiment
  extractMorePseudonymousNetworkFeaturesWherePaid : EvidenceAcquisitionExperiment
  acquireFreshDevelopmentRowsBeforeHoldout : EvidenceAcquisitionExperiment

acquisitionPriority : EvidenceAcquisitionExperiment → Nat
acquisitionPriority recoverMoreMeetingDurations = 6
acquisitionPriority recoverMediationDurations = 6
acquisitionPriority countResolvedTabledAndUnresolvedItems = 5
acquisitionPriority auditDocumentaryCompleteness = 6
acquisitionPriority expandSourceRegimeControls = 5
acquisitionPriority extractMorePseudonymousNetworkFeaturesWherePaid = 3
acquisitionPriority acquireFreshDevelopmentRowsBeforeHoldout = 6

PreferredAcquisition : EvidenceAcquisitionExperiment → EvidenceAcquisitionExperiment → Set
PreferredAcquisition left right = acquisitionPriority right ≤ acquisitionPriority left

canonicalAcquisitionDesign : Robust.ExperimentDesign EvidenceAcquisitionExperiment Nat
canonicalAcquisitionDesign = Robust.experimentDesign acquisitionPriority PreferredAcquisition ⊤

record CoordinationBurdenExperimentBoundary : Set where
  constructor coordinationBurdenExperimentBoundary
  field
    archivalCooccurrenceIdentifiesCausalEffect observedEdgeCountIsCoordinationCost qualitativeMajorityTimeIsNumericMinutes selectedMeetingFamilyIsRandomSample sourceCompletenessAssumed experimentDesignAloneCreatesEvidence empiricalCoordinationCostFunctionalPaid quantitativeIncidenceBurdenRelationshipPaid completeNamedParticipantMatrixRequired : Bool
    participantAndIssueControlsRequired sourceCompletenessAuditRequired sourceRegimeControlRequired modelDiscrepancyMustRemainExplicit quantitativeIdentifiabilityRequired heldOutMeetingValidationRequired : Bool
open CoordinationBurdenExperimentBoundary public

canonicalExperimentBoundary : CoordinationBurdenExperimentBoundary
canonicalExperimentBoundary =
  coordinationBurdenExperimentBoundary
    false false false false false false false false false
    true true true true true true

robustnessObligations : List Robust.RobustnessObligation
robustnessObligations =
  Robust.modelDiscrepancy ∷ Robust.vectorStateParameterControl ∷ Robust.correlatedUncertainty ∷ Robust.experimentDesign ∷ Robust.quantitativeLocalIdentifiability ∷ Robust.heldOutRepairValidation ∷ []

canonicalOccupyCoordinationBurdenExperimentReceipt : GenericReceipt.GenericReceipt
canonicalOccupyCoordinationBurdenExperimentReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy coordination-burden experiment-design frontier"
    "DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact"
    "canonicalExperimentBoundary"
    "reuses the robust experiment-inference frontier and recuts the active acquisition programme after corpus materialisation toward additional duration/mediation/outcome coordinates, documentary-completeness auditing, source-regime controls and fresh development evidence; named-person reconstruction is not an objective"
    "current development diagnostics do not justify opening the protected holdout; meeting duration is not coordination cost, archival co-occurrence is descriptive only, source regime and missingness remain explicit, and no quantitative or causal incidence-to-burden relationship is paid"
    "agda -i . DASHI/Governance/OccupyCoordinationBurdenExperimentDesignRegression.agda"
