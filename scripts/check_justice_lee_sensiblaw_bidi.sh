#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Reasoning/JusticeLeeSensibLawAdversarialProofGraphBidiExact.agda
  DASHI/Reasoning/JusticeLeeSensibLawExperimentSearchCrossPollinationExact.agda
  DASHI/Reasoning/JusticeLeeSensibLawBidiSearchClosureExact.agda
)

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "missing Justice Lee/SensibLaw BIDI source: $file" >&2; exit 1; }
  if grep -nE '\b(postulate|{-# *TERMINATING *#}|{-# *NON_TERMINATING *#})\b' "$file"; then
    echo "forbidden proof escape found in $file" >&2
    exit 1
  fi
done

grep -q 'compileSearchObligation' DASHI/Reasoning/JusticeLeeSensibLawBidiSearchClosureExact.agda
grep -q 'typedResidualAloneDeterminesGloballyOptimalEvidenceProbeIsFalse' DASHI/Reasoning/JusticeLeeSensibLawBidiSearchClosureExact.agda
grep -q 'graphAdmissionMayInventUnreceiptedPredicateIsFalse' DASHI/Reasoning/JusticeLeeSensibLawBidiSearchClosureExact.agda
grep -q 'legalAdjudicationIsLeanKernelVerificationIsFalse' DASHI/Reasoning/JusticeLeeSensibLawExperimentSearchCrossPollinationExact.agda
grep -q 'silentlyDeletesWeakArgumentsIsFalse' DASHI/Reasoning/JusticeLeeSensibLawAdversarialProofGraphBidiExact.agda

echo 'Justice Lee × SensibLaw BIDI structural checks passed'
