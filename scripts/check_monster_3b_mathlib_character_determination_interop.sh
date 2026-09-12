#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BMathlibCharacterDeterminationInteropExact.agda"

if [[ ! -f "$OWNER" ]]; then
  echo "missing owner: $OWNER" >&2
  exit 1
fi

required=(
  "record MathlibCharacterDeterminationCoordinate"
  "d131ae62882df478bb2aadf013181b4c5b31b328"
  "scalar_product_char_eq_finrank_equivariant"
  "char_orthonormal"
  "import DASHI.Wikimedia.IbrahimMonster3BCyclotomicScalarExtensionInteropExact as ScalarExtension"
  "cyclotomicScalarExtensionFrontier"
  "scalarExtensionPaid"
  "record DashiToMathlibCharacterDeterminationTransport"
  "compileIrreducibleCharacterDetermination"
  "mathlibTheoremDoesNotCreateDashiTransport"
  "oeisHasCharacterDeterminationAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing mathlib character-determination interop surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B mathlib character-determination interop check: ok"
