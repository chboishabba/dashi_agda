#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

target=DASHI/Moonshine/OggSSP2BNormWeldLastLeafExact.agda
test -f "$target"

grep -q 'targetSocleFrobeniusRuntimePaid' "$target"
grep -q 'blockProjectorExistenceSourced' "$target"
grep -q 'blockNaturalityIsCompilerConsequence' "$target"
grep -q 'normEquivarianceIsCompilerConsequence' "$target"
grep -q 'actualCentralizerActionInstantiationPaid' "$target"
grep -q 'actualResidualBlockActionInstantiationPaid' "$target"
grep -q 'actualTateExteriorSquareWeldPaid' "$target"
grep -q 'remainingSameObjectLeafCountIsOne' "$target"

scripts/run_agda29_parallel_check.sh "$target"
