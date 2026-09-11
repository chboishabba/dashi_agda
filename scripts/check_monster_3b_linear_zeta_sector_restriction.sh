#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BLinearZetaSectorRestrictionExact.agda"

required=(
  "record LinearSingleActionProducer"
  "singleActionProducer"
  "ambientLinearCarrier"
  "ambientCarrierIsActualState"
  "centralActionIsLinear"
  "normalizerActionIsLinear"
  "phaseScalingIsLinear"
  "zetaLinearCarrier"
  "zetaCarrierIsLiteralEigenspace"
  "inertiaRestrictionIsLinear"
  "setLevelPhaseResolutionDoesNotCreateLinearSector"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing required linear zeta-sector restriction surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B linear zeta-sector restriction check: ok"
