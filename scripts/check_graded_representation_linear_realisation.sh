#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/GradedRepresentationLinearRealisationExact.agda"

required=(
  "record LinearEndomorphismRealisation"
  "linearCarrier"
  "endomorphismEvaluation"
  "toRepresentationCarrier"
  "fromRepresentationCarrier"
  "representationAfterLinear"
  "linearAfterRepresentation"
  "evaluatedEnd"
  "evaluatedEndPreservesZero"
  "evaluatedEndPreservesAddition"
  "evaluatedEndPreservesScaling"
  "groupLinearAction"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing graded representation linear-realisation surface: $needle" >&2
    exit 1
  fi
done

echo "graded representation linear realisation check: ok"
