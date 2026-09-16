#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricSelectedSectionActionRealizationExact.agda"

[[ -f "$owner" ]]

grep -q 'record SelectedSectionActionRealization' "$owner"
grep -q 'realizeAction' "$owner"
grep -q 'actionRealizationCommutes' "$owner"
grep -q 'realizeActionTrace' "$owner"
grep -q 'selectedActionTraceRealizationCommutes' "$owner"
grep -q 'finiteActionRealization' "$owner"
grep -q 'consumerFutureSafetyAloneImpliesPhysicalRealization' "$owner"
grep -q 'canonicalSelectedSectionActionRealizationBoundary' "$owner"
