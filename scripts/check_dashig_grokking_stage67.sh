#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
  DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"
  if grep -nE '\b(postulate|{-# *OPTIONS +--allow-unsolved-metas|unsafe|primTrustMe)\b|\?|{!!}' "$f"; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

grep -q '013962fb839e83ce8e4b35486fe1a79792c96db8' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'https://github.com/SPUTNIKAI/LeechTransformer.git' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'metaIntrospectorCloneImpliesMetaIntrospectorAuthorship' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'secondaryReadmeCitationIsPrimaryAttributionReceipt' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q '10.5281/zenodo.18784424' DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
grep -q 'currentPrelimDoesNotIdentifyFutureArchitectureWinner' DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
grep -q 'geometryMeasurementClosesWinnerEnvelope' DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
grep -q 'plainMeasurementClosesWinnerEnvelope' DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/Reasoning/DASHIgGrokkingEmpiricalBridgeExact.agda
  agda -i . -i src DASHI/Reasoning/DASHIgGrokkingStage67SpecimenExact.agda
else
  echo "agda unavailable: structural DASHIg attribution/Stage-6/7 scan completed; no kernel-clean claim"
fi
