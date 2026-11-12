#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Governance/CybersynGlobalViabilityMaxCutExact.agda
  DASHI/Governance/CybersynPhysicalFinanceCutExact.agda
  DASHI/Governance/CybersynAuthorityFeedbackExact.agda
  DASHI/Governance/CybersynCrossSectorScenarioExact.agda
  DASHI/Governance/CybersynGlobalViabilityEverything.agda
)

for f in "${files[@]}"; do
  test -f "$f" || { echo "MISSING: $f" >&2; exit 1; }
  if grep -nE '^([[:space:]]*)postulate([[:space:]]|$)|\\{![^}]*!\\}|--allow-unsolved-metas|--(unsafe|type-in-type|no-positivity-check|no-termination-check)' "$f"; then
    echo "Forbidden unsafe option/postulate/hole in $f" >&2
    exit 1
  fi
done

for theorem in \
  headlineCannotRecoverCommunityResult \
  financedButUnaccountableNotViable \
  announcementCannotFixHousingUse \
  earlyHarmBlocksWholeHorizon \
  investorReportCannotRecoverEffect \
  consultationNotAdmission \
  twoShocksTrigger \
  yenAndCollateralTrigger \
  pressureIsNotPublicGuaranteeAdmission; do
  grep -R -q "^$theorem :" "${files[@]}" || {
    echo "Missing theorem surface: $theorem" >&2; exit 1;
  }
done

if ! command -v agda >/dev/null 2>&1; then
  echo "Agda unavailable: no kernel acceptance; use pinned Nix/Agda 2.9 environment." >&2
  exit 2
fi

echo "Agda executable: $(command -v agda)"
agda --version
# Additional local stdlib paths are to be passed through normal Agda library
# configuration; this script does not assume CI or external services.
agda -i . DASHI/Governance/CybersynGlobalViabilityEverything.agda
echo "Focused Cybersyn global viability root checked in local Agda."
