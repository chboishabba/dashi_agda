#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanP33FiniteWeightedSchurSquaredExact.agda
  DASHI/Physics/YangMills/BalabanP33CombesThomasSquaredHalfGapExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasSchurExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCoordinateBasisExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalQuadraticToSquaredCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasEntryDecayExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasQuadraticEndgameExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound20Validation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round twenty contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'BalabanP33FiniteWeightedSchurSquaredExact.agda:weightedGramIdentity'
  'BalabanP33FiniteWeightedSchurSquaredExact.agda:finiteWeightedCauchySquared'
  'BalabanP33FiniteWeightedSchurSquaredExact.agda:finiteSchurSquared'
  'BalabanP33FiniteWeightedSchurSquaredExact.agda:finiteSymmetricSchurSquared'
  'BalabanP33CombesThomasSquaredHalfGapExact.agda:halfGapSquaredSurvives'
  'BalabanP33CombesThomasSquaredHalfGapExact.agda:p33SquaredHalfGapSurvives'
  'BalabanP33CombesThomasSquaredHalfGapExact.agda:matrixDifferenceApplyExact'
  'BalabanP33CombesThomasSquaredHalfGapExact.agda:sameVectorTiltDecomposition'
  'BalabanP33CombesThomasSquaredHalfGapExact.agda:sameVectorReverseTriangleSquared'
  'BalabanP33PhysicalCombesThomasSchurExact.agda:physicalTiltDefectColumnBelowHalfGap'
  'BalabanP33PhysicalCombesThomasSchurExact.agda:physicalTiltDefectSchurSquared'
  'BalabanP33PhysicalCombesThomasSchurExact.agda:physicalTiltedSquaredLower'
  'BalabanP33PhysicalCombesThomasSchurExact.agda:rowMassFromStencilDegreeBudget'
  'BalabanP33PhysicalCoordinateBasisExact.agda:physicalIdentitySelectorExact'
  'BalabanP33PhysicalCoordinateBasisExact.agda:physicalBasisNormSqExact'
  'BalabanP33PhysicalCoordinateBasisExact.agda:physicalMatrixApplyBasisExact'
  'BalabanP33PhysicalCoordinateBasisExact.agda:physicalMatrixEntrySquaredFromOperatorBound'
  'BalabanP33PhysicalCoordinateBasisExact.agda:squareBound4096ImpliesAbsoluteBound64'
  'BalabanP33PhysicalQuadraticToSquaredCoercivityExact.agda:originalSquaredLowerFromQuadratic'
  'BalabanP33PhysicalQuadraticToSquaredCoercivityExact.agda:physicalOriginalSquaredCoercivityFromQuadratic'
  'BalabanP33PhysicalCombesThomasEntryDecayExact.agda:physicalMatrixApplyCompositionExact'
  'BalabanP33PhysicalCombesThomasEntryDecayExact.agda:physicalTiltedInverseSquaredOperatorBound'
  'BalabanP33PhysicalCombesThomasEntryDecayExact.agda:physicalTiltedGreenEntryBound'
  'BalabanP33PhysicalCombesThomasEntryDecayExact.agda:physicalGreenKernelDecayFromSquaredData'
  'BalabanP33PhysicalCombesThomasQuadraticEndgameExact.agda:squaredResolventFromQuadratic'
  'BalabanP33PhysicalCombesThomasQuadraticEndgameExact.agda:physicalGreenKernelDecayFromQuadraticCoercivity'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

# Provenance and scope discipline.
grep -q '10.1007/BF01646473' \
  DASHI/Physics/YangMills/BalabanP33CombesThomasSquaredHalfGapExact.agda
grep -q 'arXiv:0709.3707' \
  DASHI/Physics/YangMills/BalabanP33CombesThomasSquaredHalfGapExact.agda
grep -q '10.1007/s11512-013-0191-2' \
  DASHI/Physics/YangMills/BalabanP33CombesThomasSquaredHalfGapExact.agda
grep -q '10.1007/s11425-016-0311-4' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasSchurExact.agda
grep -q 'not itself symmetric' \
  DASHI/Physics/YangMills/BalabanP33FiniteWeightedSchurSquaredExact.agda
grep -q 'stencil degree and coefficient size enter' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasSchurExact.agda
grep -q 'trace-ideal and faster-than-polynomial' \
  DASHI/Physics/YangMills/BalabanP33CombesThomasSquaredHalfGapExact.agda
grep -q 'tilted entry bound is produced' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasEntryDecayExact.agda
grep -q 'No independent squared-coercivity premise' \
  DASHI/Physics/YangMills/BalabanP33PhysicalCombesThomasQuadraticEndgameExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound20Validation.agda
