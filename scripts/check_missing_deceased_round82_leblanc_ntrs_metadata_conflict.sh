#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Culture/MissingDeceasedTwentyScientistRound82LeBlancNTRSMetadataConflictExact.agda"

test -f "$owner"
grep -q 'catalogMeetingMetadataPaid = true' "$owner"
grep -q 'attachmentWorkshopMetadataPaid = true' "$owner"
grep -q 'metadataConflictVisible = true' "$owner"
grep -q 'catalogDoesNotOverwriteAttachment = true' "$owner"
grep -q 'attachmentDoesNotOverwriteCatalog = true' "$owner"
grep -q 'h2Paid = false' "$owner"
grep -q 'h3Paid = false' "$owner"
