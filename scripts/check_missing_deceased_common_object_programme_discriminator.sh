#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"

owner="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeDiscriminatorExact.agda"
events="$root/DASHI/Culture/MissingDeceasedEventTimeConcentrationExact.agda"
fixture="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeInvestigationExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$events"
test -f "$fixture"
test -f "$agg"

grep -q 'data HypothesisClass' "$owner"
grep -q 'record CandidateProgramme' "$owner"
grep -q 'record CandidateObject' "$owner"
grep -q 'record RequiredCapability' "$owner"
grep -q 'record PersonCapabilityReceipt' "$owner"
grep -q 'record CrossPersonProgrammeReceipt' "$owner"
grep -q 'data EventClass' "$owner"
grep -q 'record EventChronologyReceipt' "$owner"
grep -q 'record HypothesisDiscriminationReceipt' "$owner"

grep -q 'longDurationAutonomousExtremeEnvironment' "$owner"
grep -q 'highEnergyExperimentalInfrastructure' "$owner"
grep -q 'advancedPropulsionAnomalousFieldTestbed' "$owner"
grep -q 'strategicRDPortfolio' "$owner"

grep -q 'capabilityFitPaysProgrammeIdentity = false' "$owner"
grep -q 'temporalClusterPaysCoordination = false' "$owner"
grep -q 'programmeIdentityPaysTargeting = false' "$owner"
grep -q 'geographyPaysCommonCause = false' "$owner"
grep -q 'technicalAdjacencyPaysCommonProgramme = false' "$owner"
grep -q 'commonObjectRequiresLiteralCrossPersonReceipt = true' "$owner"
grep -q 'coordinatedTargetingRequiresOperationalEvidence = true' "$owner"
grep -q 'portfolioObjectMembershipRequiresSameObjectReceipt = true' "$owner"
grep -q 'sourceRepetitionPaysIndependentCorroboration = false' "$owner"

grep -q 'populationLevelSignificancePaid = false' "$events"
grep -q 'calendarProximityPaysCausalProximity = false' "$events"
grep -q 'publicationDateEqualsWorkDate = false' "$events"

grep -q 'literalCrossPersonReceiptCount' "$fixture"
grep -q 'h3OperationalEvidencePaid = false' "$fixture"
grep -q 'searchResidualCreatesKnownAbsence = false' "$fixture"

grep -q 'MissingDeceasedCommonObjectProgrammeDiscriminatorExact' "$agg"
grep -q 'MissingDeceasedEventTimeConcentrationExact' "$agg"
grep -q 'MissingDeceasedCommonObjectProgrammeInvestigationExact' "$agg"

echo 'Common-object/programme discriminator static contract: OK'
