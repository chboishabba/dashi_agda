#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Cognition/RecursiveFibreTowerGateSeparationExact.agda"

[[ -f "$owner" ]]

grep -q 'triadicHeightZeroCardinalityAgrees' "$owner"
grep -q 'triadicHeightOneCardinalityAgrees' "$owner"
grep -q 'triadicHeightTwoCardinalityAgrees' "$owner"
grep -q 'phaseRefinementPreservesBaseObservation' "$owner"
grep -q 'towerOpeningIsNotWithinChartRefinement' "$owner"
grep -q 'matchingCardinalityDoesNotIdentifyCarriers' "$owner"
grep -q 'canonicalRecursiveFibreTowerGateBoundary' "$owner"
