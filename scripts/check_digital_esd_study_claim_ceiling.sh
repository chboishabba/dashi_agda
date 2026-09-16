#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDStudyClaimCeilingExact.agda
REGRESSION=DASHI/Education/DigitalESDStudyClaimCeilingRegression.agda
BRIDGE=DASHI/Education/DigitalESDStudyClaimMethodBridgeExact.agda
METHOD_REGRESSION=DASHI/Education/DigitalESDManuscriptMethodologyRegression.agda
AGG=DASHI/EverythingDigitalESDReciprocalBraid.agda
DOC=docs/digital-esd-study-claim-ceiling.md
ROADMAP=docs/digital-esd-roadmap-experimental-design-addendum.md

for file in "$OWNER" "$REGRESSION" "$BRIDGE" "$METHOD_REGRESSION" "$AGG" "$DOC" "$ROADMAP"; do
  [[ -f "$file" ]] || { echo "missing study-claim-ceiling source: $file" >&2; exit 1; }
done

for file in "$OWNER" "$REGRESSION" "$BRIDGE" "$METHOD_REGRESSION"; do
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^import DASHI.Core.AttributedSourceCore as Attr$' "$OWNER"
grep -q '^  source : Attr.AttributedSource$' "$OWNER"
grep -q '^studyClaimCoordinateCount : Nat$' "$OWNER"
grep -q 'enrolledOrReportedNCoordinate' "$OWNER"
grep -q 'analysisNCoordinate' "$OWNER"
grep -q 'attritionMissingnessCoordinate' "$OWNER"
grep -q 'effectSizeCoordinate' "$OWNER"
grep -q 'uncertaintyIntervalCoordinate' "$OWNER"
grep -q 'implicationCeilingCoordinate' "$OWNER"
grep -q '^reportedPValueDoesNotCreateCausalIdentification :' "$OWNER"
grep -q '^largeSampleDoesNotCreateRepresentativePopulation :' "$OWNER"
grep -q '^confidenceIntervalDoesNotCreatePopulationTransport :' "$OWNER"
grep -q '^qualitativeFindingDoesNotCreatePopulationPrevalence :' "$OWNER"
grep -q '^studyFindingDoesNotCreateSystemTransformation :' "$OWNER"
grep -q '^missingUncertaintyMayNotBeInvented :' "$OWNER"
grep -q '^canonicalStudyClaimCeilingBoundary :' "$OWNER"

grep -q '^effectiveExtractionCoordinateCount : Nat$' "$BRIDGE"
grep -q '^studyClaimCeilingBoundary :' "$BRIDGE"
grep -q '^canonicalStudyClaimMethodBoundary :' "$BRIDGE"
grep -q 'effectiveExtractionCoordinateCount ≡ 20' "$METHOD_REGRESSION"
grep -q 'studyClaimBridgePinsCeilingRegression' "$METHOD_REGRESSION"

grep -q '^import DASHI.Education.DigitalESDStudyClaimCeilingExact$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDStudyClaimCeilingRegression$' "$AGG"
grep -q '^import DASHI.Education.DigitalESDStudyClaimMethodBridgeExact$' "$AGG"

grep -q '20 effective top-level extraction coordinates' "$DOC"
grep -q 'reported/enrolled sample size' "$DOC"
grep -q 'confidence-interval surface' "$DOC"
grep -q 'claim ceiling' "$ROADMAP"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION" "$METHOD_REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
  agda -i . "$METHOD_REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "digital ESD study claim ceiling source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
