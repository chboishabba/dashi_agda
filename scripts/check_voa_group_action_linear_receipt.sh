#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/VertexOperatorAlgebraLinearActionReceiptExact.agda"

required=(
  "record GradedModuleVectorSpaceReceipt"
  "record VOAGroupActionLinearReceipt"
  "moduleCarrier"
  "zeroAdditiveIdentity"
  "additionAssociative"
  "scalarDistributesAddition"
  "scalarAssociative"
  "actionPreservesZero"
  "actionPreservesAddition"
  "actionPreservesScaling"
  "voaAutomorphismLinearityIsSourceDefinition"
  "opaquePreservesModesDoesNotCreateLinearity"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing old-VOA linearity receipt surface: $needle" >&2
    exit 1
  fi
done

echo "old VOA group-action linearity receipt check: ok"
