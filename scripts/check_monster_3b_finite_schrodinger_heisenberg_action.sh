#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Moonshine/Monster3BFiniteSchrodingerHeisenbergActionExact.agda"

[[ -f "$OWNER" ]] || { echo "missing owner: $OWNER" >&2; exit 1; }

required=(
  "heisenbergAction :"
  "H.Heisenberg6 → Schrodinger.SchrodingerFunction → Schrodinger.SchrodingerFunction"
  "actionExponent"
  "translateByVector"
  "identityActionPointwise"
  "translationGeneratorAgreement"
  "modulationGeneratorAgreement"
  "centralGeneratorAgreement"
  "actionPreservesAddition"
  "actionPreservesCyclotomicScaling"
  "record FullHeisenbergActionLawReceipt"
  "actionFormulaConstructed"
  "generatorCompatibilityPaid"
  "exactCyclotomicLinearityPaid"
  "fullActionLawPaid"
  "generatorActionsDoNotCreateFullGroupAction"
  "10.1017/CBO9780511626265"
  "10.1112/S1461157000001352"
  "A005052"
  "oeisHasActionAuthority"
)

for needle in "${required[@]}"; do
  grep -Fq "$needle" "$OWNER" || {
    echo "missing finite Schrodinger Heisenberg-action surface: $needle" >&2
    exit 1
  }
done

echo "monster 3B finite Schrodinger Heisenberg action check: ok"
