#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact.agda"

required=(
  "chenLamShimakura"
  "10.1007/s00209-017-1878-z"
  "1606.05961"
  "record Z3OrbifoldPhaseReceipt"
  "threeSummandZ3GradingPaid"
  "phaseEigenvaluesOneXiXiSquaredPaid"
  "fullAutomorphismGroupMonsterPaid"
  "threeLocalShapePaid"
  "sourceDoesNotCreateZetaModelBasisChart"
  "sourceDoesNotCreateTranslationIntertwiners"
  "sourceDoesNotCreateModulationIntertwiners"
  "oeisHasRecognitionAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing Z3 orbifold phase-recognition snowball surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B Z3-orbifold phase-recognition snowball check: ok"
