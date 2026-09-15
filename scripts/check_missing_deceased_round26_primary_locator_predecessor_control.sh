#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"
owner="$root/DASHI/Culture/MissingDeceasedTwentyScientistRound26PrimaryLocatorPredecessorControlExact.agda"
agg="$root/DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda"

test -f "$owner"
test -f "$agg"

grep -q 'record SourcePaymentSurface' "$owner"
grep -q 'primaryLocatorPaid : Bool' "$owner"
grep -q 'primaryBytesCustodyPaid : Bool' "$owner"
grep -q 'sameObjectSemanticsPaid : Bool' "$owner"
grep -q 'crossPersonIdentityPaid : Bool' "$owner"
grep -q 'armyFY2001LocatorPaid = true' "$owner"
grep -q 'armyFY2001BytesCustodyPaid = false' "$owner"
grep -q 'nasaNCC8124PrimaryBytesPaid = true' "$owner"
grep -q 'nasaPredecessorCannotPayArmySameProgramme = true' "$owner"
grep -q 'jplSharedWorkPackageLocated = false' "$owner"
grep -q 'nudtSharedTaskLocated = false' "$owner"
grep -q 'round26H2PaidCount = 0' "$owner"
grep -q 'round26H3PaidCount = 0' "$owner"
grep -q 'MissingDeceasedTwentyScientistRound26PrimaryLocatorPredecessorControlExact' "$agg"

echo 'Round26 primary-locator/predecessor-control static contract: OK'
