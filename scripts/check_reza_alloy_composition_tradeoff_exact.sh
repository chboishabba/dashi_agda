#!/usr/bin/env bash
set -euo pipefail
root="${1:-.}"
owner="$root/DASHI/Physics/Materials/RezaBurnResistantAlloyCompositionTradeoffExact.agda"
test -f "$owner"
grep -q 'example1CompositionSumTenths = 1000' "$owner"
grep -q 'example2CompositionSumTenths = 1000' "$owner"
grep -q 'example1CompositionCloses = refl' "$owner"
grep -q 'example2CompositionCloses = refl' "$owner"
grep -q 'example2HigherTensileStrength = true' "$owner"
grep -q 'example1HigherExtinguishingThreshold = true' "$owner"
grep -q 'observedTradeoffDoesNotCreateUniversalMonotonicLaw = false' "$owner"
echo 'Reza composition/tradeoff static contract: OK'
