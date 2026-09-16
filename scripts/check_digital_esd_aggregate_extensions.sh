#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

AGG=DASHI/EverythingDigitalESDReciprocalBraid.agda
CANONICAL_REGRESSION=DASHI/Education/DigitalESDCanonicalOwnerRegression.agda
for file in "$AGG" "$CANONICAL_REGRESSION"; do
  [[ -f "$file" ]] || { echo "missing digital ESD aggregate source: $file" >&2; exit 1; }
done

grep -q '^import DASHI.Education.DigitalESDCrossRoundAttributionBoundaryExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDAcquisitionSnowballRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDParticipantGovernanceContextTransferRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDPaperTypeRequirementRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDConsumerRelativeLifecycleExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDConsumerRelativeLifecycleRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDStructuredSearchExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDStructuredSearchRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDCanonicalOwnerRegression$' "$AGG"
grep -q '^crossRoundAttributionOwnerRegression :' "$CANONICAL_REGRESSION"

echo "digital ESD aggregate extension source audit passed"
