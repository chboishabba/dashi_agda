#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BActualVOASelected3BCompositionExact.agda"

required=(
  "record ActualVOASelected3BComposition"
  "recognizedActionSource"
  "recognizedBridgeIsLiteralSameObjectBridge"
  "compiledSingleActionProducerIsAcquisitionProducer"
  "recognizedSourceDoesNotCreateLinearity"
  "bridgeEqualityDoesNotCreateActionIntertwiner"
  "A005052"
  "oeisHasCompositionAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing actual VOA selected-3B composition surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B actual VOA selected-3B composition check: ok"
