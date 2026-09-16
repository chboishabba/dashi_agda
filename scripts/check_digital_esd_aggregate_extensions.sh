#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGG=DASHI/EverythingDigitalESDReciprocalBraid.agda
[[ -f "$AGG" ]] || { echo "missing aggregate: $AGG" >&2; exit 1; }

grep -q '^import DASHI.Education.DigitalESDCrossRoundAttributionBoundaryExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDAcquisitionSnowballRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDPaperTypeRequirementRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDConsumerRelativeLifecycleExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDConsumerRelativeLifecycleRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDCanonicalOwnerRegression$' "$AGG"

echo "digital ESD aggregate extension source audit passed"
