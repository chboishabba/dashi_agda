#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BActualLinearMultiplicityAcquisitionExact.agda"

required=(
  "record ActualLinearMultiplicityAcquisition"
  "literalSameObjectWeld"
  "literalVOALinearityReceipt"
  "sameLiteralZetaSector"
  "degree17496SameObject"
  "degree113724SameObject"
  "sourcePaidCharacterOnSameAction"
  "literalVOALinearityReceiptInterfaceAvailable"
  "literalActionSameObjectWeldAvailable"
  "homogeneousGradeLinearisationInterfaceAvailable"
  "actualMonsterVOALinearityReceiptPaid"
  "actualLinearActionPaid"
  "actualTwelveSeventyEightIntertwinerPaid"
  "A005052"
  "oeisHasActionAuthority"
  "degreeOccurrenceDoesNotCreateAction"
  "permutationBasisDoesNotCreateLinearAction"
)

for needle in "${required[@]}"; do
  if ! grep -Fq "$needle" "$OWNER"; then
    echo "missing actual-linear multiplicity acquisition surface: $needle" >&2
    exit 1
  fi
done

echo "monster 3B actual-linear multiplicity acquisition check: ok"
