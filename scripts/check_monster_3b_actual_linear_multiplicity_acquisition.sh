#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"
OWNER="$ROOT/DASHI/Wikimedia/IbrahimMonster3BActualLinearMultiplicityAcquisitionExact.agda"

required=(
  "record ActualLinearMultiplicityAcquisition"
  "literalSameObjectWeld"
  "literalVOALinearityReceipt"
  "gradeTwoLinearRealisation"
  "weightTwoLinearBridge"
  "gradeTwoRealisationIsWeightTwoRealisation"
  "weightTwoConstituentCarrierIsSelected3BAmbient"
  "selected3BStateCarrierEquality"
  "record Selected3BNormalizerMonsterActionWeld"
  "normalizerToMonster"
  "normalizerActionIntertwines"
  "degree17496SameObject"
  "degree113724SameObject"
  "sourcePaidCharacterOnSameAction"
  "selected3BNormalizerMonsterActionWeldRequired"
  "sourceNativeInertiaSameActionPaid"
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
