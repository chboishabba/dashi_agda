#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/GradedVOAHomogeneousLinearRealisationExact.agda"

required=(
  "record HomogeneousGradeLinearRealisation"
  "actionData"
  "grade"
  "linearEndomorphismRealisation"
  "toHomogeneous"
  "fromHomogeneous"
  "homogeneousAfterLinear"
  "linearAfterHomogeneous"
  "scalarToVOA"
  "zeroCompatibility"
  "additionCompatibility"
  "scalingCompatibility"
  "opaqueGradingCompatibilityDoesNotCreateLinearGrade"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing graded VOA homogeneous linear-realisation surface: $needle" >&2
    exit 1
  fi
done

echo "graded VOA homogeneous linear realisation check: ok"
