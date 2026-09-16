#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricPantsGluingBridgeExact.agda"

[[ -f "$owner" ]]

grep -q 'record HyperfabricPantsGluing' "$owner"
grep -q 'realizeChannel' "$owner"
grep -q 'seamInterface' "$owner"
grep -q 'InterfaceMatch' "$owner"
grep -q 'canonicalPantsGluing' "$owner"
grep -q 'seamDoesNotAutomaticallyConstructNewHyperfabric' "$owner"
grep -q 'canonicalTypedHyperfabricPantsGluingBoundary' "$owner"
