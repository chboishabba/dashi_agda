#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound36HCBContractDerivativeIdentityExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record ContractDerivativeIdentityReceipt' "$owner"
grep -q 'contractIdentifier = "FA9300-07-C-0001"' "$owner"
grep -q 'round36DerivativeReceiptCount = 2' "$owner"
grep -q 'round36RetainedScientistDerivativeCount = 0' "$owner"
grep -q 'derivativeInventorListIsNotExhaustiveContractRoster = true' "$owner"
grep -q 'absenceFromDerivativeCannotPayNonParticipation = true' "$owner"
grep -q 'derivativeIdentityCanPayNamedTechnicalParticipation = true' "$owner"
grep -q 'round36H2PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound36HCBContractDerivativeIdentityExact' "$agg"

echo 'Round36 HCB contract-derivative identity static contract: OK'
