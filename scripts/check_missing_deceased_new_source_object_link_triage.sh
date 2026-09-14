#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedNewSourceObjectLinkTriageExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
grep -q 'data SourceObjectRole' "$owner"
grep -q 'rezaMondaloyPatentObject' "$owner"
grep -q 'rezaHydrocarbonBoostApplicationObject' "$owner"
grep -q 'maiwaldSURPObject' "$owner"
grep -q 'grillmairStreamScienceObject' "$owner"
grep -q 'chenHardwareVerificationObject' "$owner"
grep -q 'trinityClathrateControl' "$owner"
grep -q 'wormholeTheoryControl' "$owner"
grep -q 'chavezPoliceLead' "$owner"
grep -q 'dbeConsultingIdentityCollision' "$owner"
grep -q 'primarySciencePaysCommonProgramme = false' "$owner"
grep -q 'secondaryEventAggregationPaysOperationalLink = false' "$owner"
grep -q 'sameBusinessNamePaysSameEntity = false' "$owner"
grep -q 'MissingDeceasedNewSourceObjectLinkTriageExact' "$agg"

echo 'New-source object-link triage static contract: OK'
