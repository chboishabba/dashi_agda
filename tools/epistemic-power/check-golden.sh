#!/usr/bin/env bash
# Local-only, explicit Agda Golden gate for PR #1479.
# No CI dependency. Run from repository root with the pinned Agda 2.9
# and the repository's matching standard-library installation.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
if ! command -v agda >/dev/null 2>&1; then
  echo "BLOCKED: agda executable unavailable; no kernel acceptance receipt" >&2
  exit 127
fi
agda --version
modules=(
  DASHI/Governance/EpistemicPowerStructuralRetentionExact.agda
  DASHI/Governance/EpistemicPowerHistoryAndNonSubstitutionExact.agda
  DASHI/Governance/EpistemicPowerCapacityDynamicsExact.agda
  DASHI/Governance/EpistemicPowerCostPayoffExact.agda
  DASHI/Governance/EpistemicPowerQueryAdequacyCapstoneExact.agda
  DASHI/Governance/EpistemicPowerMinimalObserverRepairExact.agda
  DASHI/Governance/EpistemicPowerSourceAtlasExact.agda
  DASHI/Governance/EpistemicPowerCrossDomainCapstoneExact.agda
)
for module in "${modules[@]}"; do
  echo "=== Golden checking: $module"
  agda --safe -i . "$module"
done
echo "Golden source modules accepted by the Agda kernel (see version above)."
