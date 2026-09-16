#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Cognition/PNF/FibreNaturalDeltaInverseLimitExact.agda"

[[ -f "$owner" ]]

grep -q 'record CoherentDeltaFamily' "$owner"
grep -q 'deltaCoherent' "$owner"
grep -q 'applyCoherentDeltaToInverseLimit' "$owner"
grep -q 'projectionNaturality' "$owner"
grep -q 'identityTowerDelta' "$owner"
grep -q 'canonicalZeroUpdatedRemainsCoherent' "$owner"
grep -q 'deltaUpdateDoesNotOpenTowerLevel' "$owner"
grep -q 'canonicalFibreNaturalDeltaInverseLimitBoundary' "$owner"
