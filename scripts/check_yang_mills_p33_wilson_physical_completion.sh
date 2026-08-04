#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33QuaternionScalarCyclicityExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonPlacementQuaternionAtomIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonRightInsertedCrossAtomsExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonDiagonalChartAtomsExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonCrossOperatorPythagoreanExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalContourLength24Exact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalPathStageBudgetExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonPhysicalCompletionValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "Wilson physical completion tranche contains a postulate or hole" >&2
  exit 1
fi

grep -q 'scalarPartFiveFactorCyclic' \
  DASHI/Physics/YangMills/BalabanP33QuaternionScalarCyclicityExact.agda
grep -q 'scalarPartUnitConjugationInvariant' \
  DASHI/Physics/YangMills/BalabanP33QuaternionScalarCyclicityExact.agda
grep -q 'placementAtomsMatchGeneratedProductRule' \
  DASHI/Physics/YangMills/BalabanP33WilsonPlacementQuaternionAtomIdentificationExact.agda
grep -q 'cross01Factorisation' \
  DASHI/Physics/YangMills/BalabanP33WilsonRightInsertedCrossAtomsExact.agda
grep -q 'cross23Factorisation' \
  DASHI/Physics/YangMills/BalabanP33WilsonRightInsertedCrossAtomsExact.agda
grep -q 'secondAt3NormalForm' \
  DASHI/Physics/YangMills/BalabanP33WilsonDiagonalChartAtomsExact.agda
grep -q 'unitSandwichImaginaryPythagorean' \
  DASHI/Physics/YangMills/BalabanP33WilsonCrossOperatorPythagoreanExact.agda
grep -q 'p33PhysicalInverseSquaredBoundForPositivePreimage' \
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda
grep -q 'minimalCenteredContourLengthAtMost24' \
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalContourLength24Exact.agda
grep -q 'minimalContourTransportBudget' \
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalPathStageBudgetExact.agda
grep -q 'minimalContourPathDerivativeBudget' \
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalPathStageBudgetExact.agda

grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33WilsonRightInsertedCrossAtomsExact.agda
grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33WilsonRightInsertedCrossAtomsExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33WilsonCrossOperatorPythagoreanExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda
grep -q '10.1007/BF01215223' \
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalContourLength24Exact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP33WilsonPhysicalCompletionValidation.agda
