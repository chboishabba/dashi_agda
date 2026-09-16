#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Cognition/FibreBraidActionTraceExact.agda"

[[ -f "$owner" ]]

grep -q 'data ReasoningStrand' "$owner"
grep -q 'auxiliaryCrossing' "$owner"
grep -q 'reasoningBraidTrace' "$owner"
grep -q 'evaluateReasoningTrace' "$owner"
grep -q 'traceRealizesTransportBraid' "$owner"
grep -q 'canonicalTraceLowersDefect' "$owner"
grep -q 'sameEndpointDifferentOrderedTrace' "$owner"
grep -q 'orderedTracesAreDistinct' "$owner"
grep -q 'traceDoesNotPromoteBraidGroup' "$owner"
