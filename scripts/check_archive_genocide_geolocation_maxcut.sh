#!/usr/bin/env bash
set -euo pipefail

OWNER="DASHI/Governance/ArchiveGenocideGeolocationAntiTargetingExact.agda"
VALIDATION="DASHI/Governance/ArchiveGenocideGeolocationAntiTargetingValidation.agda"

[ -f "$OWNER" ]
[ -f "$VALIDATION" ]

grep -q "archiveGenocideGeolocationSource" "$OWNER"
grep -q "LocationPrecision" "$OWNER"
grep -q "GeolocationReviewState" "$OWNER"
grep -q "EventTimeBasis" "$OWNER"
grep -q "GeolocationOrigin" "$OWNER"
grep -q "GeolocationEvidence" "$OWNER"
grep -q "coarsen" "$OWNER"
grep -q "rivalFineClaimsAgreeCoarsely" "$OWNER"
grep -q "rivalFineClaimsRemainDistinct" "$OWNER"
grep -q "coarseObserverIsConsumerSufficient" "$OWNER"
grep -q "coarseObserverIsLeastSufficient" "$OWNER"
grep -q "coarseObserverCannotServeFineConsumer" "$OWNER"
grep -q "EvidenceConsumer" "$OWNER"
grep -q "operationalTargetingConsumerIsNotEvidenceConsumer" "$OWNER"
grep -q "SafeDisclosureReceipt" "$OWNER"
grep -q "protectedNearRealTimeExactReleaseImpossible" "$OWNER"
grep -q "minimumSufficientObserverRequired" "$OWNER"
grep -q "provenanceMustSurviveDisclosure" "$OWNER"
grep -q "conflictMustRemainVisible" "$OWNER"
grep -q "reviewDoesNotCreateExactness" "$OWNER"
grep -q "thirdPartyCreditMustRemainDistinct" "$OWNER"
grep -q "antiPanopticonBoundaryAnchor" "$OWNER"
grep -q "consumerDescentBoundaryAnchor" "$OWNER"
grep -q "archiveGenocideGeolocationMaxCutBoundary" "$OWNER"

grep -q "rivalFineAgreementValidated" "$VALIDATION"
grep -q "rivalFineDistinctnessValidated" "$VALIDATION"
grep -q "fineConsumerNonDescentValidated" "$VALIDATION"
grep -q "targetingConsumerBlockedValidated" "$VALIDATION"
grep -q "protectedLiveExactBlockedValidated" "$VALIDATION"
grep -q "provenanceRetentionValidated" "$VALIDATION"
