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
  "0a9d695f4f24c0f9fad00116cfa4c840451dd3de"
  "scalar_product_char_eq_finrank_equivariant"
  "finrank_hom_simple_simple_eq_zero_of_not_iso"
  "algebraicallyClosedFieldRequiredForChosenRoute"
  "equalCharactersForceNonzeroEquivariantHom"
  "nonzeroSimpleMorphismIsIso"
  "record LeanEqualCharacterSimpleIsoReceipt"
  "record DashiToMathlibCharacterDeterminationTransport"
  "leanEqualCharacterSimpleIsoReceipt"
  "compileIrreducibleCharacterDetermination"
  "algebraicClosureIsNotRequiredForChosenRoute"
  "mathlibTheoremDoesNotCreateDashiTransport"
  "oeisHasCharacterDeterminationAuthority"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing mathlib character-determination interop surface: $needle" >&2
    exit 1
  fi
done

# The chosen proof route must not silently retain the superseded scalar-extension
# dependency as a proof prerequisite.
if grep -Fq "scalarExtension : ScalarExtension.Cyclotomic3ScalarExtension" "$OWNER"; then
  echo "superseded scalar-extension prerequisite still present in character-determination transport" >&2
  exit 1
fi

echo "monster 3B mathlib character-determination interop check: ok"
