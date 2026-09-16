#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricActionCrossingTransportExact.agda"

[[ -f "$owner" ]]

grep -q 'record HyperfabricCrossingTransport' "$owner"
grep -q 'crossingStep' "$owner"
grep -q 'transportTrace' "$owner"
grep -q 'ActionTrace' "$owner"
grep -q 'traceOrderRemainsProvenance' "$owner"
grep -q 'transportDoesNotImplyCrossingReversibility' "$owner"
grep -q 'transportDoesNotPromoteTraceToBraidGroup' "$owner"
grep -q 'canonicalTypedHyperfabricActionCrossingBoundary' "$owner"
