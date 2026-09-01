#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
  DASHI/RegulatoryAssayExperimentProofSearchValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required assay experiment/proof-search source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^assaySearchGraph :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
grep -q '^realFindingRequiresEightLeaves :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
grep -q '^experimentCannotDirectlyCloseProofLeaf :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
grep -q '^expandedBundleIsLanguageExtension :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
grep -q '^tableMembershipAloneProvesLabScope :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda
grep -q '^nonDetectAloneProvesAbsence :' DASHI/Chemistry/RegulatoryAssayExperimentProofSearchExact.agda

scripts/run_agda29_parallel_check.sh DASHI/RegulatoryAssayExperimentProofSearchValidation.agda
