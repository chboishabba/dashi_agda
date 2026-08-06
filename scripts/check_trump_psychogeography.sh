#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round10_psychogeography.sh

files=(
  DASHI/Biology/TrumpPsychogeographicPolicyAtlasExact.agda
  DASHI/Biology/TrumpPsychogeographicHexagramTestsExact.agda
  DASHI/Biology/TrumpPsychogeographyAuthorityBoundary.agda
  DASHI/Biology/TrumpPsychogeographyEverything.agda
  DASHI/Biology/TrumpPsychogeographyValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "Trump psychogeography tranche contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'TrumpPsychogeographicPolicyAtlasExact.agda:immigrationRaidsMassDeportationCase'
  'TrumpPsychogeographicPolicyAtlasExact.agda:palantirSurveillanceProcurementCase'
  'TrumpPsychogeographicPolicyAtlasExact.agda:candidateProjectionReachesSpatialMobilisation'
  'TrumpPsychogeographicHexagramTestsExact.agda:unitaryAndAdministrativeProfilesCoincide'
  'TrumpPsychogeographicHexagramTestsExact.agda:immigrationAndPalestineCasesRemainDistinct'
  'TrumpPsychogeographicHexagramTestsExact.agda:borderWallDiffersFromImmigrationAtOneLine'
  'TrumpPsychogeographicHexagramTestsExact.agda:immigrationMovingTestChangesTwoLines'
  'TrumpPsychogeographicHexagramTestsExact.agda:palantirMovingTestChangesTwoLines'
  'TrumpPsychogeographyAuthorityBoundary.agda:existingTrumpLaneRemainsNonPromoting'
  'TrumpPsychogeographyAuthorityBoundary.agda:policySourcesDoNotCreateLegalConclusions'
  'TrumpPsychogeographyAuthorityBoundary.agda:sharedHexagramDoesNotCollapsePolicyCases'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Biology/$file"
done

grep -q '603 U.S. 593' DASHI/Biology/TrumpPsychogeographicPolicyAtlasExact.agda
grep -q 'H. Rept. 117-663' DASHI/Biology/TrumpPsychogeographicPolicyAtlasExact.agda
grep -q 'PIID 70CTD026FC0000018' DASHI/Biology/TrumpPsychogeographicPolicyAtlasExact.agda
grep -q 'zeroMeansCentristCompromise' DASHI/Biology/TrumpPsychogeographicHexagramTestsExact.agda
grep -q 'procurementRecordProvesSurveillanceAbuse' DASHI/Biology/TrumpPsychogeographicPolicyAtlasExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/TrumpPsychogeographyValidation.agda
