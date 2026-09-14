#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedLiteralCrossPersonIdentifierSearchExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
grep -q 'data CrossPersonRelationClass' "$owner"
grep -q 'amyNamesNingHAL5' "$owner"
grep -q 'houseOversightPostEventAggregation' "$owner"
grep -q 'ningArmyIdentifierSinglePersonOnly' "$owner"
grep -q 'rezaHardwickMcCaslandIntermediatedChain' "$owner"
grep -q 'mondaloy2020ContractIdentifier' "$owner"
grep -q 'literalPersonReferencePaysCommonProgramme = false' "$owner"
grep -q 'postEventGovernmentAggregationPaysPreEventLinkage = false' "$owner"
grep -q 'singlePersonProgrammeIdentifierPaysCrossPersonLink = false' "$owner"
grep -q 'intermediatedInstitutionalChainPaysDirectProfessionalLink = false' "$owner"
grep -q 'preMediaCrossCaseOperationalIdentifierPaid = false' "$owner"
grep -q 'literalCommonProgrammeIdentifierCount = 0' "$owner"
grep -q 'MissingDeceasedLiteralCrossPersonIdentifierSearchExact' "$agg"

echo 'Literal cross-person identifier search static contract: OK'
