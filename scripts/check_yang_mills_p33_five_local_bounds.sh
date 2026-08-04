#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33LiteralBondCellIncidenceExact.agda
  DASHI/Physics/YangMills/BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda
  DASHI/Physics/YangMills/BalabanP33PrimitiveAbsoluteOperatorAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33SU2EuclideanGeometryExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopLowOrderTaylorBracketsExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopTaylorPolynomialFormExact.agda
  DASHI/Physics/YangMills/BalabanP33BishopSU2AdDexpNumeratorBoundsExact.agda
  DASHI/Physics/YangMills/BalabanP33SU2Radius8192EnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanP33SU2QuadraticPrimitiveNormAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDerivativeDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralCovariantDivergenceDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33FourStageOperatorDifferenceExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalContourLength24Exact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109MinimalPathStageBudgetExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109FourStageAllocatedBudgetExact.agda
  DASHI/Physics/YangMills/BalabanP33CMP109DerivativeDifferencePrimitiveExact.agda
  DASHI/Physics/YangMills/BalabanP33SignedFiniteAtomExpansionExact.agda
  DASHI/Physics/YangMills/BalabanP33AbsoluteFiniteAtomAdapterExact.agda
  DASHI/Physics/YangMills/BalabanP33ConfiguredSignedAtomListsExact.agda
  DASHI/Physics/YangMills/BalabanP33CurvatureAtomGeometryExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonPlaquetteSecondVariationPlacementsExact.agda
  DASHI/Physics/YangMills/BalabanP33QuaternionProductSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonPlaquetteScalarSecondVariationExact.agda
  DASHI/Physics/YangMills/BalabanP33WilsonTransportedInnerProductExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveSandwichSignedFormExact.agda
  DASHI/Physics/YangMills/BalabanP33SandwichLocalFamilyExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveSandwichLocalCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33IdentityCurvatureLocalExact.agda
  DASHI/Physics/YangMills/BalabanP33LiteralFiveMechanismFamiliesExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2FiniteCoordinatesExact.agda
  DASHI/Physics/YangMills/BalabanP33ThreeComponentCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2MatrixCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33RationalInverseNorm32Exact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteWeightedRowSumContractionExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteWeightedSupportCountHalfExact.agda
  DASHI/Physics/YangMills/BalabanP33WeightedNeumannHalfContractionExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveLocalPhysicalBoundsValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "P33 hard-math tranche contains an explicit postulate or hole" >&2
  exit 1
fi

checks=(
  'BalabanP33LiteralBondCellIncidenceExact.agda:bondCellChargeSumExact'
  'BalabanP33PrimitiveOperatorNormLocalBoundsExact.agda:transportCoefficientBound'
  'BalabanP33PrimitiveAbsoluteOperatorAdapterExact.agda:operatorNormDominatesCoordinate'
  'BalabanP33SU2EuclideanGeometryExact.agda:adNormSqIsFourGramGap'
  'BalabanP33SU2EuclideanGeometryExact.agda:adCubicGammaTwoExact'
  'BalabanP33BishopLowOrderTaylorBracketsExact.agda:lowOrderTaylorBrackets'
  'BalabanP33BishopTaylorPolynomialFormExact.agda:defectTaylorBounds'
  'BalabanP33BishopSU2AdDexpNumeratorBoundsExact.agda:adScalarNumeratorBelowTaylorEnvelope'
  'BalabanP33BishopSU2AdDexpNumeratorBoundsExact.agda:dexpScalarNumeratorBelowTaylorEnvelope'
  'BalabanP33SU2Radius8192EnvelopeExact.agda:adEnvelopeAtHalfRadiusBelowConfiguredRadius'
  'BalabanP33SU2Radius8192EnvelopeExact.agda:dexpPairEnvelopeAtRadiusBelowTwiceRadius'
  'BalabanP33SU2QuadraticPrimitiveNormAdapterExact.agda:dexpPairNormBelowTwoRadius'
  'BalabanP33LiteralCovariantDerivativeDifferenceExact.agda:covariantDerivativeDifferenceExact'
  'BalabanP33LiteralCovariantDivergenceDifferenceExact.agda:covariantDivergenceDifferenceExact'
  'BalabanP33FourStageOperatorDifferenceExact.agda:fourStageDifferenceExact'
  'BalabanP33CMP109MinimalContourLength24Exact.agda:minimalCenteredContourLengthAtMost24'
  'BalabanP33CMP109MinimalPathStageBudgetExact.agda:minimalContourTransportBudget'
  'BalabanP33CMP109MinimalPathStageBudgetExact.agda:minimalContourPathDerivativeBudget'
  'BalabanP33CMP109FourStageAllocatedBudgetExact.agda:fourStageAllocatedBudgetGivesRadius'
  'BalabanP33CMP109DerivativeDifferencePrimitiveExact.agda:blockDerivativeDifferenceNormBelowRadius'
  'BalabanP33SignedFiniteAtomExpansionExact.agda:sumMappedTwoSided'
  'BalabanP33ConfiguredSignedAtomListsExact.agda:configuredSignedAtomsGivePath4PhysicalCoercivity'
  'BalabanP33CurvatureAtomGeometryExact.agda:curvatureAtomsAreGeometricDecomposition'
  'BalabanP33WilsonPlaquetteSecondVariationPlacementsExact.agda:plaquetteSecondVariationPlacementCountExact'
  'BalabanP33QuaternionProductSecondVariationExact.agda:fourFactorSecondVariationIsSixteenAtomSum'
  'BalabanP33WilsonPlaquetteScalarSecondVariationExact.agda:fourLinkWilsonSecondVariationIsSixteenScalarAtoms'
  'BalabanP33WilsonTransportedInnerProductExact.agda:explicitConjugationScalarProduct'
  'BalabanP33FiveSandwichSignedFormExact.agda:constraintSignedFormBound'
  'BalabanP33SandwichLocalFamilyExact.agda:localSandwichRemainderBound'
  'BalabanP33FiveSandwichLocalCoercivityExact.agda:fiveSandwichLocalChannelsGiveP33Floor'
  'BalabanP33IdentityCurvatureLocalExact.agda:identityCurvatureCellExact'
  'BalabanP33LiteralFiveMechanismFamiliesExact.agda:literalFiveMechanismsGivePath4PhysicalCoercivity'
  'BalabanP33PhysicalSU2FiniteCoordinatesExact.agda:encodePhysicalSU2NormSqExact'
  'BalabanP33PhysicalSU2FiniteCoordinatesExact.agda:physicalMatrixQuadraticRealizationExact'
  'BalabanP33ThreeComponentCoercivityExact.agda:threeComponentP33Floor'
  'BalabanP33PhysicalSU2MatrixCoercivityExact.agda:physicalP33FloorTransfersToEveryCoordinate'
  'BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda:p33PhysicalInverseSquaredBoundForPositivePreimage'
  'BalabanP33RationalInverseNorm32Exact.agda:p33InverseNormAtMostThirtyTwo'
  'BalabanP33FiniteWeightedRowSumContractionExact.agda:weightedKernelContraction'
  'BalabanP33FiniteWeightedSupportCountHalfExact.agda:asHalfWeightedRowContraction'
  'BalabanP33WeightedNeumannHalfContractionExact.agda:weightedResidualHalfPowerBound'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Source metadata required on the files where the external theorem enters.
grep -q 'arXiv:2205.08354' DASHI/Physics/YangMills/BalabanP33BishopTaylorPolynomialFormExact.agda
grep -q 'arXiv:1108.1335' DASHI/Physics/YangMills/BalabanP33CMP109MinimalContourLength24Exact.agda
grep -q '10.1007/BF01215223' DASHI/Physics/YangMills/BalabanP33CMP109FourStageAllocatedBudgetExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanP33QuaternionProductSecondVariationExact.agda
grep -q '10.1007/978-3-319-13467-3' DASHI/Physics/YangMills/BalabanP33WilsonTransportedInnerProductExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanP33PhysicalSU2CauchyInverseSquaredExact.agda
grep -q '10.1103/PhysRevD.10.2445' DASHI/Physics/YangMills/BalabanP33WilsonPlaquetteScalarSecondVariationExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP33FiveLocalPhysicalBoundsValidation.agda
