#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BCyclotomicScalarExtensionInteropExact.agda"

if [[ ! -f "$OWNER" ]]; then
  echo "missing owner: $OWNER" >&2
  exit 1
fi

required=(
  "record Cyclotomic3ScalarExtension"
  "preservesAddition"
  "preservesMultiplication"
  "preservesZeta"
  "targetAlgebraicallyClosedCharacteristicZero"
  "record SchrodingerScalarExtensionTransport"
  "translationActionPreserved"
  "modulationActionPreserved"
  "scalarExtensionDoesNotCreateFDRepCharacterTransport"
  "10.1007/978-1-4612-1934-7"
  "A005052"
  "oeisHasScalarExtensionAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing cyclotomic scalar-extension interop surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B cyclotomic scalar-extension interop check: ok"
