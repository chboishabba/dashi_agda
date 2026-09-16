#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OWNER=DASHI/Education/DigitalESDAcquisitionSnowballParetoExact.agda
REGRESSION=DASHI/Education/DigitalESDAcquisitionSnowballRegression.agda
ICT_OWNER=DASHI/Education/DigitalESDICTLifecycleCircularitySnowballExact.agda
ICT_REGRESSION=DASHI/Education/DigitalESDICTLifecycleCircularitySnowballRegression.agda

for file in "$OWNER" "$REGRESSION" "$ICT_OWNER" "$ICT_REGRESSION"; do
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

# Refined ICT lifecycle / circularity method child.  Methods may pay method
# coordinates, but the parent's same-object durability/lifecycle residual stays
# unpaid until intervention-specific evidence exists.
grep -q 'ITU-T L.1410 (11/2024)' "$ICT_OWNER"
grep -q 'ITU-T L.1023 (08/2023)' "$ICT_OWNER"
grep -q '^canonicalICTLifecycleCircularityAcquisition :' "$ICT_OWNER"
grep -q '^ictLifecycleMethodDoesNotPayDeploymentInventory :' "$ICT_OWNER"
grep -q '^circularityMethodDoesNotPayDeploymentCircularity :' "$ICT_OWNER"
grep -q '^circularityMethodDoesNotProveDeploymentDurability :' "$ICT_OWNER"
grep -q '^l1410LifecycleBidi :' "$ICT_OWNER"
grep -q '^l1023CircularityBidi :' "$ICT_OWNER"
grep -q '^parentOpenDurabilityRemainsUnpaid :' "$ICT_OWNER"
grep -q '^currentRefinedLifecycleFrontier :' "$ICT_OWNER"
grep -q '^l1410MethodPaidRegression :' "$ICT_REGRESSION"
grep -q '^l1023CircularityMethodPaidRegression :' "$ICT_REGRESSION"
grep -q '^l1410DoesNotPaySameObjectInventoryRegression :' "$ICT_REGRESSION"
grep -q '^l1023DoesNotPayDeploymentCircularityRegression :' "$ICT_REGRESSION"
grep -q '^methodDoesNotPayDurabilityRegression :' "$ICT_REGRESSION"
grep -q '^parentResidualStillUnpaidRegression :' "$ICT_REGRESSION"
grep -q '^refinedSameObjectLifecycleResidualRegression :' "$ICT_REGRESSION"
grep -q '^refinedHardwareCircularityResidualRegression :' "$ICT_REGRESSION"

if command -v nix >/dev/null 2>&1 && [[ -x scripts/run_agda29_parallel_check.sh ]]; then
  scripts/run_agda29_parallel_check.sh "$ICT_REGRESSION"
  scripts/run_agda29_parallel_check.sh "$REGRESSION"
elif command -v agda >/dev/null 2>&1; then
  agda -i . "$ICT_REGRESSION"
  agda -i . "$REGRESSION"
elif [[ "${1:-}" == "--source-only" ]]; then
  echo "acquisition snowball source audit passed; Agda kernel receipt unobserved (--source-only explicitly selected)"
else
  echo "Agda kernel check unavailable: agda executable not found" >&2
  exit 2
fi
