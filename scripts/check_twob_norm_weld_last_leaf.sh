#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

leaf=DASHI/Moonshine/OggSSP2BNormWeldLastLeafExact.agda
frontier=DASHI/Moonshine/OggSSP2BPostSocleMaxCutExact.agda
for target in "$leaf" "$frontier"; do test -f "$target"; done

grep -q 'targetSocleFrobeniusRuntimePaid' "$leaf"
grep -q 'blockProjectorExistenceSourced' "$leaf"
grep -q 'blockNaturalityIsCompilerConsequence' "$leaf"
grep -q 'normEquivarianceIsCompilerConsequence' "$leaf"
grep -q 'actualCentralizerActionInstantiationPaid' "$leaf"
grep -q 'actualResidualBlockActionInstantiationPaid' "$leaf"
grep -q 'actualTateExteriorSquareWeldPaid' "$leaf"
grep -q 'remainingSameObjectLeafCountIsOne' "$leaf"

grep -q 'remainingNormWeldSameObjectLeavesIsOne' "$frontier"
grep -q 'remainingDefectSourceBitsIsTwo' "$frontier"
grep -q 'actualCentralizerBlockActionStillOpen' "$frontier"
grep -q 'actualTateExteriorSquareWeldStillOpen' "$frontier"

scripts/run_agda29_parallel_check.sh "$leaf" "$frontier"
