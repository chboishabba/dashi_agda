module DASHI.Governance.OccupyCoordinationBurdenExperimentDesignRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyCoordinationBurdenExperimentDesignExact as Design

incidencePredictorRequired :
  Design.requiresIncidenceMeasurement Design.canonicalMeasurementRequirements ≡ true
incidencePredictorRequired = refl

meetingDurationRequired :
  Design.requiresMeetingDuration Design.canonicalMeasurementRequirements ≡ true
meetingDurationRequired = refl

mediationTimeRequired :
  Design.requiresMediationTime Design.canonicalMeasurementRequirements ≡ true
mediationTimeRequired = refl

participantCountControlRequired :
  Design.requiresParticipantCountControl Design.canonicalMeasurementRequirements ≡ true
participantCountControlRequired = refl

issueCountControlRequired :
  Design.requiresIssueCountControl Design.canonicalMeasurementRequirements ≡ true
issueCountControlRequired = refl

currentArchiveDoesNotPayCostFunctional :
  Design.empiricalCoordinationCostFunctionalPaid Design.canonicalExperimentBoundary ≡ false
currentArchiveDoesNotPayCostFunctional = refl

cooccurrenceDoesNotPayCausality :
  Design.archivalCooccurrenceIdentifiesCausalEffect Design.canonicalExperimentBoundary ≡ false
cooccurrenceDoesNotPayCausality = refl

heldOutValidationRequired :
  Design.heldOutMeetingValidationRequired Design.canonicalExperimentBoundary ≡ true
heldOutValidationRequired = refl
