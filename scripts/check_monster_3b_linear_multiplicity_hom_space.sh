#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BLinearMultiplicityHomSpaceExact.agda"

required=(
  "record ActualLinearMultiplicityHomSpace"
  "EquivariantMap"
  "evaluationMap"
  "evaluationInverse"
  "inverseAfterEvaluation"
  "evaluationAfterInverse"
  "sameObjectLinearRepresentation"
  "cocycleCompensatedAction"
  "cocycleMultiplicityIsSameLinearCarrier"
  "cocycleTensorIsChosenZetaCarrier"
  "characterDoesNotCreateHomEvaluation"
  "finiteBasisEvaluationDoesNotCreateLinearHomEvaluation"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing required linear multiplicity Hom-space surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B linear multiplicity Hom-space check: ok"
