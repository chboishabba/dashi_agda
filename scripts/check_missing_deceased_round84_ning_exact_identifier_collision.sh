#!/usr/bin/env bash
set -euo pipefail

target='DASHI/Culture/MissingDeceasedTwentyScientistRound84NingExactIdentifierCollisionExact.agda'

test -f "$target"
grep -q 'sameIdentifierStringDoesNotPaySameObject' "$target"
grep -q 'texasAuditSurfaceDoesNotPayACGravityOutcome' "$target"
grep -q 'semanticMismatchRequiresIdentityBridge' "$target"
grep -q 'universalNonParticipationStillUnproved' "$target"
