#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33LiteralBondCellIncidenceExact.agda
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
  DASHI/Physics/YangMills/BalabanP33PrimitiveAbsoluteOperatorAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33SU2QuadraticPrimitiveNormAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDerivativeDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDivergenceDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33FourStageOperatorDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109DerivativeDifferencePrimitiveExact.agda
  DASHI/Physics/YangMills/BalabanP33SignedFiniteAtomExpansionExact.agda
  DASHI/Physics/YangMills/BalabanP33AbsoluteFiniteAtomAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33ConfiguredSignedAtomListsExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveSandwichSignedFormExact.agda
  DASHI/Physics/YangMills/BalabanP33SandwichLocalFamilyExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveSandwichLocalCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33IdentityCurvatureLocalExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
  DASHI/Physics/YangMills/BalabanP33RationalInverseNorm32Exact.agda
  DASHI/Physics/YangMills/BalabanP33WeightedNeumannHalfContractionExact.agda
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
grep -q 'transportCoefficientBound' \
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
grep -q 'operatorNormDominatesCoordinate' \
  DASHI/Physics/YangMills/BalabanP33PrimitiveAbsoluteOperatorAdapterExact.agda
grep -q 'dexpPairNormBelowTwoRadius' \
  DASHI/Physics/YangMills/BalabanP33SU2QuadraticPrimitiveNormAdapterExact.agda
grep -q 'covariantDerivativeDifferenceExact' \
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDerivativeDifferenceExact.agda
grep -q 'covariantDivergenceDifferenceExact' \
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDivergenceDifferenceExact.agda
grep -q 'fourStageDifferenceExact' \
  DASHI/Physics/YangMills/BalabanP33FourStageOperatorDifferenceExact.agda
grep -q 'blockDerivativeDifferenceNormBelowRadius' \
  DASHI/Physics/YangMills/BalabanP33CMP109DerivativeDifferencePrimitiveExact.agda
grep -q 'sumMappedTwoSided' \
  DASHI/Physics/YangMills/BalabanP33SignedFiniteAtomExpansionExact.agda
grep -q 'fromAbsoluteFixedAtomExpansion' \
  DASHI/Physics/YangMills/BalabanP33AbsoluteFiniteAtomAdapterExact.agda
grep -q 'configuredSignedAtomsGivePath4PhysicalCoercivity' \
  DASHI/Physics/YangMills/BalabanP33ConfiguredSignedAtomListsExact.agda
grep -q 'constraintSignedFormBound' \
  DASHI/Physics/YangMills/BalabanP33FiveSandwichSignedFormExact.agda
grep -q 'localSandwichRemainderBound' \
  DASHI/Physics/YangMills/BalabanP33SandwichLocalFamilyExact.agda
grep -q 'fiveSandwichLocalChannelsGiveP33Floor' \
  DASHI/Physics/YangMills/BalabanP33FiveSandwichLocalCoercivityExact.agda
grep -q 'identityCurvatureCellExact' \
  DASHI/Physics/YangMills/BalabanP33IdentityCurvatureLocalExact.agda
grep -q 'literalFiveMechanismsGivePath4PhysicalCoercivity' \
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
grep -q 'p33InverseNormAtMostThirtyTwo' \
  DASHI/Physics/YangMills/BalabanP33RationalInverseNorm32Exact.agda
grep -q 'weightedResidualHalfPowerBound' \
  DASHI/Physics/YangMills/BalabanP33WeightedNeumannHalfContractionExact.agda

grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDivergenceDifferenceExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33ConfiguredSignedAtomListsExact.agda
grep -q '10.1007/978-3-319-13467-3' \
  DASHI/Physics/YangMills/BalabanP33SU2QuadraticPrimitiveNormAdapterExact.agda
grep -q '10.1007/978-3-642-66282-9' \
  DASHI/Physics/YangMills/BalabanP33FourStageOperatorDifferenceExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanP33FiveSandwichLocalCoercivityExact.agda
grep -q '10.1007/BF01215223' \
  DASHI/Physics/YangMills/BalabanP33CMP109DerivativeDifferencePrimitiveExact.agda
grep -q '10.1103/PhysRevD.10.2445' \
  DASHI/Physics/YangMills/BalabanP33IdentityCurvatureLocalExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP33FiveLocalPhysicalBoundsValidation.agda
