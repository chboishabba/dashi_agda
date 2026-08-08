#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round37.sh

files=(
  DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTAdmissibleProjectorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedVariationKKTMultiplierExact.agda
  DASHI/Physics/YangMills/BalabanWilsonBooleanFourCubeExact.agda
  DASHI/Physics/YangMills/BalabanWilsonMobiusAtomDecompositionExact.agda
  DASHI/Physics/YangMills/BalabanWilsonD4SubsetCharacterExact.agda
  DASHI/Physics/YangMills/BalabanP33OrientedWilsonD4TransportExact.agda
  DASHI/Physics/YangMills/BalabanSelectedVariationResidualOwnershipExact.agda
  DASHI/Physics/YangMills/BalabanP33ReducedPhysicalHessianExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTPseudoinverseProjectorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedConstraintAnnihilatorKKTExact.agda
  DASHI/Physics/YangMills/BalabanSelectedRawExtractorConstraintDefectExact.agda
  DASHI/Physics/YangMills/BalabanP33SingletonBudgetFeasibilityExact.agda
  DASHI/Physics/YangMills/BalabanP33NonorthogonalPhysicalFrameExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockGreenAlgebraExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockGreenExact.agda
  DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockTiltExact.agda
  DASHI/Physics/YangMills/BalabanP33CovariantD4TransportCocycleBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanP33PhysicalFactorRoleDeepEnvelopeExact.agda
  DASHI/Physics/YangMills/BalabanYangMillsGapAuthorityHierarchyExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound39PseudoinverseKKTValidation.agda
)

doc=Docs/support/reference/YangMillsPseudoinverseKKTGreenRound39.md
index=Docs/support/reference/YangMillsReferenceIndex.md

for file in "${files[@]}" "$doc" "$index"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported|emptyCoordinate|chooseEmpty|chooseCoordinate' "${files[@]}"; then
  echo "round thirty nine contains a hole, postulate, unsafe escape, trust primitive, imported theorem receipt, or invalid generic selector" >&2
  exit 1
fi

if grep -nE '\((data|field)[[:space:]]*:' "${files[@]}"; then
  echo "round thirty nine uses an Agda reserved keyword as a typed binder" >&2
  exit 1
fi

checks=(
  'BalabanP33FiniteKKTAdmissibleProjectorExact.agda:selectedProjectedVariationUniqueNearestAdmissible'
  'BalabanSelectedVariationKKTMultiplierExact.agda:projectorDefectFirstVariationMultiplierIdentity'
  'BalabanWilsonMobiusAtomDecompositionExact.agda:mobiusAfterZetaExact'
  'BalabanWilsonD4SubsetCharacterExact.agda:namedD4CountExact'
  'BalabanP33OrientedWilsonD4TransportExact.agda:transportFrameCompositionExact'
  'BalabanSelectedVariationResidualOwnershipExact.agda:exactCancellationRemovedBeforeMajorisation'
  'BalabanP33ReducedPhysicalHessianExact.agda:frameNormExact'
  'BalabanP33FiniteKKTPseudoinverseProjectorExact.agda:fullInverseToPseudoinverse'
  'BalabanP33FiniteKKTPseudoinverseProjectorExact.agda:projectSatisfiesUniversalProperty'
  'BalabanP33FiniteKKTPseudoinverseProjectorExact.agda:universalPropertyUnique'
  'BalabanSelectedConstraintAnnihilatorKKTExact.agda:finiteAnnihilatorKernelEqualsAdjointImage'
  'BalabanSelectedConstraintAnnihilatorKKTExact.agda:selectedKKTMultiplierUniquenessModuloRedundancy'
  'BalabanSelectedRawExtractorConstraintDefectExact.agda:rawExtractorConstraintDefectMatrixExact'
  'BalabanSelectedRawExtractorConstraintDefectExact.agda:rawExtractorProjectorDefectPairingExact'
  'BalabanP33SingletonBudgetFeasibilityExact.agda:balancedSplitExact'
  'BalabanP33SingletonBudgetFeasibilityExact.agda:symbolicSplitClosesSingletonBudget'
  'BalabanP33SingletonBudgetFeasibilityExact.agda:coefficientNoFitContradictsSymbolicSplit'
  'BalabanP33NonorthogonalPhysicalFrameExact.agda:reducedHessianGeneralizedFloor'
  'BalabanP33FiniteKKTBlockGreenAlgebraExact.agda:projectSubtractExact'
  'BalabanP33FiniteKKTBlockGreenExact.agda:kktBlockRightInverseExact'
  'BalabanP33FiniteKKTBlockTiltExact.agda:tiltedKKTStateDifferenceSplits'
  'BalabanP33FiniteKKTBlockTiltExact.agda:tiltedKKTRightInverseExact'
  'BalabanP33CovariantD4TransportCocycleBoundaryExact.agda:strictCompositionFromTrivialCocycle'
  'BalabanP33PhysicalFactorRoleDeepEnvelopeExact.agda:placementRoleCountExact'
  'BalabanP33PhysicalFactorRoleDeepEnvelopeExact.agda:physicalFourRoleEnvelopeFamily'
  'BalabanYangMillsGapAuthorityHierarchyExact.agda:CompleteGapPromotionChain'
  'BalabanYangMillsGapAuthorityHierarchyExact.agda:finiteIsNotOS'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1017/S0305004100030401' DASHI/Physics/YangMills/BalabanP33FiniteKKTPseudoinverseProjectorExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedConstraintAnnihilatorKKTExact.agda
grep -q '10.1007/BF01211042' DASHI/Physics/YangMills/BalabanSelectedRawExtractorConstraintDefectExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanP33FiniteKKTBlockTiltExact.agda
grep -q '10.1007/BF01645738' DASHI/Physics/YangMills/BalabanYangMillsGapAuthorityHierarchyExact.agda
grep -q '10.1007/BF01608978' DASHI/Physics/YangMills/BalabanYangMillsGapAuthorityHierarchyExact.agda

grep -q '55/18874368' "$doc"
grep -q 'dS((I-P) w_' "$doc"
grep -q 'Local KKT block' "$doc"
grep -q 'OSReconstructedHamiltonianGap' "$doc"
grep -Fq '[Round 39 — redundancy-safe KKT projector and local constrained Green algebra](./YangMillsPseudoinverseKKTGreenRound39.md)' "$index"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound39PseudoinverseKKTValidation.agda
