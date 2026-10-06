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
-- problem exposed by the People's Library minutes.
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

------------------------------------------------------------------------
-- Observable / control vocabulary.
------------------------------------------------------------------------

data BurdenOutcome : Set where
  totalMeetingDuration : BurdenOutcome
  mediationTime : BurdenOutcome
  tabledAgendaItems : BurdenOutcome
  unresolvedAgendaItems : BurdenOutcome
  processInterruptions : BurdenOutcome
  explicitConflictFlag : BurdenOutcome


data RequiredControl : Set where
  participantCountControl : RequiredControl
  issueCountControl : RequiredControl
  meetingTypeControl : RequiredControl
  externalShockControl : RequiredControl
  sourceCompletenessControl : RequiredControl
  repeatedParticipantControl : RequiredControl

record CoordinationBurdenMeasurementRequirements : Set where
  constructor coordinationBurdenMeasurementRequirements
  field
    requiresIncidenceMeasurement : Bool
    requiresMeetingDuration : Bool
    requiresMediationTime : Bool
    requiresTabledItemCount : Bool
    requiresDecisionCount : Bool
    requiresParticipantCountControl : Bool
    requiresIssueCountControl : Bool
    requiresMeetingTypeControl : Bool
    requiresExternalShockControl : Bool
    requiresSourceCompletenessAudit : Bool
    requiresRepeatedParticipantHandling : Bool

open CoordinationBurdenMeasurementRequirements public

canonicalMeasurementRequirements : CoordinationBurdenMeasurementRequirements
canonicalMeasurementRequirements =
  coordinationBurdenMeasurementRequirements
    true true true true true true true true true true true

------------------------------------------------------------------------
-- Existing archival packet expressed at the measurement interface.
--
-- Only measurements actually paid by the current archive are populated.
-- Qualitative phrases such as "majority of our time" are not converted to
-- invented minutes.
------------------------------------------------------------------------

oct15CurrentMeasurement : MeetingMeasurement
oct15CurrentMeasurement =
  meetingMeasurement
    "People's Library first formal Working Group meeting 2011-10-15"
    (Duration.sourceURL Duration.oct15FirstFormalMeeting)
    unmeasured
    unmeasured
    unmeasured
    (measured 180)
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    false

oct22CurrentMeasurement : MeetingMeasurement
oct22CurrentMeasurement =
  meetingMeasurement
    "People's Library Working Group 2011-10-22"
    (Duration.sourceURL Duration.oct22Meeting)
    (measured 18)
    unmeasured
    unmeasured
    (measured 155)
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    false

nov28CurrentMeasurement : MeetingMeasurement
nov28CurrentMeasurement =
  meetingMeasurement
    "People's Library Working Group 2011-11-28"
    Archive.minutesIndexURL
    (measured 7)
    (measured 19)
    (measured 5)
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    false

dec04CurrentMeasurement : MeetingMeasurement
dec04CurrentMeasurement =
  meetingMeasurement
    "People's Library Working Group 2011-12-04"
    Archive.minutesIndexURL
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    unmeasured
    (measured 10)
    unmeasured
    unmeasured
    false

------------------------------------------------------------------------
-- Candidate experiments are framed using the repo-generic ExperimentDesign
-- carrier. The score is only a prioritization heuristic for evidence
-- acquisition; it is not a scientific result or authority.
------------------------------------------------------------------------

data EvidenceAcquisitionExperiment : Set where
  materialiseKinnaPrichardCorpus : EvidenceAcquisitionExperiment
  extractMoreNamedMeetingEdges : EvidenceAcquisitionExperiment
  recoverMeetingStartEndTimes : EvidenceAcquisitionExperiment
  recoverMediationDurations : EvidenceAcquisitionExperiment
  countTabledAndDecidedItems : EvidenceAcquisitionExperiment
  buildHeldOutMeetingSet : EvidenceAcquisitionExperiment

acquisitionPriority : EvidenceAcquisitionExperiment → Nat
acquisitionPriority materialiseKinnaPrichardCorpus = 6
acquisitionPriority extractMoreNamedMeetingEdges = 5
acquisitionPriority recoverMeetingStartEndTimes = 5
acquisitionPriority recoverMediationDurations = 5
acquisitionPriority countTabledAndDecidedItems = 4
acquisitionPriority buildHeldOutMeetingSet = 6

PreferredAcquisition : EvidenceAcquisitionExperiment → EvidenceAcquisitionExperiment → Set
PreferredAcquisition left right = acquisitionPriority right ≤ acquisitionPriority left

canonicalAcquisitionDesign : Robust.ExperimentDesign EvidenceAcquisitionExperiment Nat
canonicalAcquisitionDesign =
  Robust.experimentDesign acquisitionPriority PreferredAcquisition ⊤

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record CoordinationBurdenExperimentBoundary : Set where
  constructor coordinationBurdenExperimentBoundary
  field
    archivalCooccurrenceIdentifiesCausalEffect : Bool
    observedEdgeCountIsCoordinationCost : Bool
    qualitativeMajorityTimeIsNumericMinutes : Bool
    selectedMeetingFamilyIsRandomSample : Bool
    sourceCompletenessAssumed : Bool
    experimentDesignAloneCreatesEvidence : Bool
    empiricalCoordinationCostFunctionalPaid : Bool
    quantitativeIncidenceBurdenRelationshipPaid : Bool

    participantAndIssueControlsRequired : Bool
    sourceCompletenessAuditRequired : Bool
    modelDiscrepancyMustRemainExplicit : Bool
    quantitativeIdentifiabilityRequired : Bool
    heldOutMeetingValidationRequired : Bool

open CoordinationBurdenExperimentBoundary public

canonicalExperimentBoundary : CoordinationBurdenExperimentBoundary
canonicalExperimentBoundary =
  coordinationBurdenExperimentBoundary
    false false false false false false false false
    true true true true true

------------------------------------------------------------------------
-- Generic robustness frontier is retained rather than redefined.
------------------------------------------------------------------------

robustnessObligations : List Robust.RobustnessObligation
robustnessObligations =
  Robust.modelDiscrepancy
  ∷ Robust.vectorStateParameterControl
  ∷ Robust.correlatedUncertainty
  ∷ Robust.experimentDesign
  ∷ Robust.quantitativeLocalIdentifiability
  ∷ Robust.heldOutRepairValidation
  ∷ []

canonicalOccupyCoordinationBurdenExperimentReceipt : GenericReceipt.GenericReceipt
canonicalOccupyCoordinationBurdenExperimentReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy coordination-burden experiment-design frontier"
    "DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact"
    "canonicalExperimentBoundary"
    "specializes the existing robust experiment-inference frontier; source-paid measurements now include 180 minutes for the first formal 15 October meeting, 155 minutes plus eighteen admitted incidence rows for 22 October, seven admitted Nov-28 rows with nineteen named attendees and five listed agenda items, and ten Dec-04 agenda items explicitly tabled because of mediation"
    "mediation duration and many controls remain unmeasured; measured meeting duration is not coordination cost, archival co-occurrence is descriptive only, and no causal incidence-to-burden relationship is paid"
    "agda -i . DASHI/Governance/OccupyCoordinationBurdenExperimentDesignRegression.agda"
