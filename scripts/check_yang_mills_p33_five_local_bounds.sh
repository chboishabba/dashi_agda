#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33LiteralBondCellIncidenceExact.agda
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveLocalPhysicalBoundsValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "Five-local-bound tranche contains an explicit postulate or hole" >&2
  exit 1
fi

grep -q 'bondCellChargeSumExact' \
  DASHI/Physics/YangMills/BalabanP33LiteralBondCellIncidenceExact.agda
grep -q 'curvatureCoefficient dataSet cell' \
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
grep -q 'transportCoefficientBound' \
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
grep -q 'literalFiveMechanismsGivePath4PhysicalCoercivity' \
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda

grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP33FiveLocalPhysicalBoundsValidation.agda
