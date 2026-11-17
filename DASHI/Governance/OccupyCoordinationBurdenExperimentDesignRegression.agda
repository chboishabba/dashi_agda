module DASHI.Governance.OccupyCoordinationBurdenExperimentDesignRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as Design

incidencePredictorRequired : Design.requiresIncidenceMeasurement Design.canonicalMeasurementRequirements ≡ true
incidencePredictorRequired = refl
meetingDurationRequired : Design.requiresMeetingDuration Design.canonicalMeasurementRequirements ≡ true
meetingDurationRequired = refl
mediationTimeRequired : Design.requiresMediationTime Design.canonicalMeasurementRequirements ≡ true
mediationTimeRequired = refl
participantCountControlRequired : Design.requiresParticipantCountControl Design.canonicalMeasurementRequirements ≡ true
participantCountControlRequired = refl
issueCountControlRequired : Design.requiresIssueCountControl Design.canonicalMeasurementRequirements ≡ true
issueCountControlRequired = refl
sourceRegimeControlRequired : Design.requiresSourceRegimeControl Design.canonicalMeasurementRequirements ≡ true
sourceRegimeControlRequired = refl

oct15DurationPaid : Design.meetingDurationMinutes Design.oct15CurrentMeasurement ≡ Design.measured 180
oct15DurationPaid = refl
oct22IncidenceRowsPaid : Design.observedIncidenceEdges Design.oct22CurrentMeasurement ≡ Design.measured 18
oct22IncidenceRowsPaid = refl
oct22DurationPaid : Design.meetingDurationMinutes Design.oct22CurrentMeasurement ≡ Design.measured 155
oct22DurationPaid = refl
nov28IncidenceRowsPaid : Design.observedIncidenceEdges Design.nov28CurrentMeasurement ≡ Design.measured 7
nov28IncidenceRowsPaid = refl
nov28NamedParticipantsPaid : Design.namedParticipantCount Design.nov28CurrentMeasurement ≡ Design.measured 19
nov28NamedParticipantsPaid = refl
nov28AgendaItemsPaid : Design.distinctIssueCount Design.nov28CurrentMeasurement ≡ Design.measured 5
nov28AgendaItemsPaid = refl
dec04TabledItemsPaid : Design.tabledAgendaItemCount Design.dec04CurrentMeasurement ≡ Design.measured 10
dec04TabledItemsPaid = refl
nov28DurationStillUnmeasured : Design.meetingDurationMinutes Design.nov28CurrentMeasurement ≡ Design.unmeasured
nov28DurationStillUnmeasured = refl
dec04MediationMinutesStillUnmeasured : Design.mediationMinutes Design.dec04CurrentMeasurement ≡ Design.unmeasured
dec04MediationMinutesStillUnmeasured = refl

namedMatrixNotRequired : Design.completeNamedParticipantMatrixRequired Design.canonicalExperimentBoundary ≡ false
namedMatrixNotRequired = refl
currentArchiveDoesNotPayCostFunctional : Design.empiricalCoordinationCostFunctionalPaid Design.canonicalExperimentBoundary ≡ false
currentArchiveDoesNotPayCostFunctional = refl
cooccurrenceDoesNotPayCausality : Design.archivalCooccurrenceIdentifiesCausalEffect Design.canonicalExperimentBoundary ≡ false
cooccurrenceDoesNotPayCausality = refl
heldOutValidationRequired : Design.heldOutMeetingValidationRequired Design.canonicalExperimentBoundary ≡ true
heldOutValidationRequired = refl
