#!/usr/bin/env bash
set -euo pipefail

ROOT="DASHI/Physics/YangMills/BalabanCMP116R281SourceResponseSameObjectRound342ValidationExact.agda"
PRODUCTION="DASHI/Physics/YangMills/BalabanCMP116R281SourceResponseSameObjectRound342Exact.agda"

for path in "$PRODUCTION" "$ROOT"; do
  test -f "$path"
done

# Static fail-closed contract before invoking Agda.
grep -q 'record SourceResponseSameObjectPayment' "$PRODUCTION"
grep -q 'record CMP109CMP116SourceResponseIdentity' "$PRODUCTION"
grep -q 'r321SameObjectBuildsB1AfterSourceIdentity' "$PRODUCTION"
grep -q 'r321SameObjectCanFeedB1AfterSourceIdentity = true' "$PRODUCTION"
grep -q 'SourceEnvelopeCalibration' "$PRODUCTION"
grep -q 'asRound341Application' "$PRODUCTION"
grep -q 'round342SourceResponseSameObjectLevel = conditional' "$PRODUCTION"
grep -q 'round342CMP109CMP116SourceIdentityLevel = conditional' "$PRODUCTION"
grep -q 'round342EnvelopeCalibrationLevel = conditional' "$PRODUCTION"
grep -q 'freshYMDecayEstimateIntroduced = false' "$PRODUCTION"
grep -q 'clayPromotion = false' "$PRODUCTION"

if command -v agda >/dev/null 2>&1; then
  agda "$ROOT"
else
  echo 'Agda executable unavailable; static contract checked only.' >&2
  exit 2
fi
