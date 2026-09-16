#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricLocalRefinementBridgeExact.agda"

[[ -f "$owner" ]]

grep -q 'record LocalStalkRefinement' "$owner"
grep -q 'refinedVertex' "$owner"
grep -q 'beforeLocalValue' "$owner"
grep -q 'afterLocalValue' "$owner"
grep -q 'requestedTransitionIsRefineWithinChart' "$owner"
grep -q 'localRefinementDoesNotOpenTower' "$owner"
grep -q 'localRefinementDoesNotIncreaseFibreDimension' "$owner"
grep -q 'localRefinementDoesNotProveExclusiveSingleStalkMutation' "$owner"
grep -q 'canonicalTypedHyperfabricLocalRefinementBoundary' "$owner"
