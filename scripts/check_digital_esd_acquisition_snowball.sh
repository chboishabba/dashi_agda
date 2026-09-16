#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
REGRESSION=DASHI/Education/DigitalESDAcquisitionSnowballRegression.agda

for file in "$OWNER" "$REGRESSION"; do
  [[ -f "$file" ]] || { echo "required acquisition-snowball source is missing: $file" >&2; exit 1; }
  if grep -nE '\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$' "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# Exact source identities acquired in this tranche.
grep -q '10.54675/ZACQ4808' "$OWNER"
grep -q '10.3390/educsci13010033' "$OWNER"
grep -q '10.1787/9997e7b3-en' "$OWNER"
grep -q '10.1007/s11367-026-02656-7' "$OWNER"
grep -q '10.1186/s41239-025-00569-3' "$OWNER"
grep -q '10.1016/j.jclepro.2024.144237' "$OWNER"
grep -q '10.1108/IJSHE-07-2021-0315' "$OWNER"
grep -q '10.1002/rev3.70029' "$OWNER"
grep -q '10.3390/su16041674' "$OWNER"
grep -q '10.1002/gch2.202300158' "$OWNER"
grep -q 'Charter for Public Digital Learning Platforms' "$OWNER"
grep -q 'Global E-waste Monitor 2024' "$OWNER"
grep -q 'Energy and AI' "$OWNER"

# Canonical attribution/snowball reuse and non-promotion surfaces.
grep -q 'Snowball.canonicalSourceRoleSnowballReceipt' "$OWNER"
grep -q '^citationDoesNotPromoteDigitalESDConclusion :' "$OWNER"
grep -q '^teachingSustainabilityWithTechnologyDoesNotPromoteSustainabilityOfTechnology :' "$OWNER"
grep -q '^oneEducationLCADoesNotEstablishUniversalOnlineSuperiority :' "$OWNER"
grep -q '^participatoryESDDoesNotPromoteConstitutiveEpistemicAuthority :' "$OWNER"
grep -q '^oneYearESDResultDoesNotPayDigitalESDLongHorizonImpact :' "$OWNER"
grep -q '^oerOrganisationalSustainabilityDoesNotPayMaterialRepairability :' "$OWNER"
grep -q '^openStandardsCharterDoesNotProvePlatformDurability :' "$OWNER"
grep -q '^rightToRepairEducationDoesNotProveDeployedHardwareRepairability :' "$OWNER"

# Pareto/snowball surfaces and residual frontier.
grep -q '^currentAcquisitionFrontier :' "$OWNER"
grep -q '^firstAcquisitionLeaf :' "$OWNER"
grep -q '^canonicalSnowballParetoBoundary :' "$OWNER"
grep -q '^participatoryESDContextRegression :' "$REGRESSION"
grep -q '^longitudinalESDBenchmarkRegression :' "$REGRESSION"
grep -q '^oerSustainabilityReviewRegression :' "$REGRESSION"
grep -q '^oerESDStudentProducerRegression :' "$REGRESSION"
grep -q '^publicPlatformInteroperabilityCharterRegression :' "$REGRESSION"
grep -q '^rightToRepairEducationRegression :' "$REGRESSION"
grep -q '^charterDoesNotProvePlatformDurabilityRegression :' "$REGRESSION"
grep -q '^repairEducationDoesNotProveRepairabilityRegression :' "$REGRESSION"
grep -q '^participantGovernanceResidualRegression :' "$REGRESSION"
grep -q '^longitudinalResidualRegression :' "$REGRESSION"
grep -q '^openDurabilityResidualRegression :' "$REGRESSION"
grep -q '^frontierStillRetainsResidualsRegression :' "$REGRESSION"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "acquisition snowball source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
