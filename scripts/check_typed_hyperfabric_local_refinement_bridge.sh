#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricLocalRefinementBridgeExact.agda"

[[ -f "$owner" ]]

grep -q 'HyperfabricNaturalDeltaSurface' "$owner"
grep -q 'HyperfabricNaturalDelta' "$owner"
grep -q 'transportDelta' "$owner"
grep -q 'restrictionNaturality' "$owner"
grep -q 'refineWithinChart' "$owner"
grep -q 'localRefinementDoesNotOpenTower' "$owner"
grep -q 'localRefinementDoesNotIncreaseFibreDimension' "$owner"
grep -q 'canonicalTypedHyperfabricLocalRefinementBoundary' "$owner"
