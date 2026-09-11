#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/MonsterWeightTwoLinearActionBridgeExact.agda"

required=(
  "record WeightTwoLinearActionBridge"
  "semanticActionBridge"
  "fullWeightTwoLinearRealisation"
  "evaluationIsSameObject"
  "constituentLinearCarrier"
  "constituentInclusion"
  "constituentDimensionIs196883"
  "constituentInvariantUnderMonsterAction"
  "constituentInclusionIntertwines"
  "semanticConstituentSetDoesNotCreateLinearSubspace"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing Monster weight-two linear action bridge surface: $needle" >&2
    exit 1
  fi
done

echo "Monster weight-two linear action bridge check: ok"
