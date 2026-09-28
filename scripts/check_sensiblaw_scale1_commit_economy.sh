#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Cognition/PNF/EditTransportLeafLocalityExact.agda
  DASHI/Cognition/PNF/IndependentFibreBatchExecutionExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerRegression.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
  DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda
  DASHI/Cognition/PNF/SensibLawSemanticBidiCampaignEverything.agda
)

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing SCALE-1.P Agda source: $file" >&2; exit 1; }
  if grep -nE '\b(postulate|{-# *TERMINATING *#}|{-# *NON_TERMINATING *#})\b' "$file"; then
    echo "forbidden proof escape found in $file" >&2
    exit 1
  fi
done

agda DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerExact.agda
agda DASHI/Cognition/PNF/SensibLawDbNativeCorpusCompilerRegression.agda

grep -q 'verifiedLocalityDoesNotImplyFewCommitBarriers'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'fewCommitBarriersDoNotProveSemanticIndependence'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'storageSyncLatencyDoesNotBecomeSemanticRecomputation'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyExact.agda
grep -q 'fixtureBatchedAuthorityMatchesSequential'   DASHI/Cognition/PNF/SensibLawDbNativeCommitEconomyRegression.agda

echo 'SCALE-1.P locality/commit-economy Agda checks passed'
