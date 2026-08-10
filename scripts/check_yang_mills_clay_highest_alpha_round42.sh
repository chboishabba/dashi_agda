#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/Common/SameSourceGluedProducerExact.agda
  DASHI/Physics/YangMills/BalabanFiniteLinearFunctionalCoordinatesExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintStencilExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramFiniteRangeExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundBlockAverageConstraintMatrixExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBlockAverageSectionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBlockAverageRowCarrierExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintGluingExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundCombinedConstraintMatrixExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRowCarrierExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintFiniteKKTExact.agda
  DASHI/Physics/YangMills/BalabanSelectedFlatGaugeReducedFloorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedGaugeRedundancyHolonomyGuardExact.agda
  DASHI/Physics/YangMills/BalabanSelectedFlatGaugeAdjointGramFloorExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRectangularTransposeFrobeniusExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeAdjointDefectExact.agda
  DASHI/Physics/YangMills/BalabanFiniteReducedFloorPerturbationExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeReducedFloorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedFlatGaugeRegularizedGreenExact.agda
  DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda
  DASHI/Physics/YangMills/BalabanVacuumOrthogonalMoscoRecoveryExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound42MasterReconciledValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round 42 contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'selectedBackgroundGaugeConstraintMatrixApplyExact' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeConstraintMatrixExact.agda
grep -q 'selectedBackgroundCombinedConstraintApplyExact' DASHI/Physics/YangMills/BalabanSelectedBackgroundCombinedConstraintMatrixExact.agda
grep -q 'selectedCombinedConstraintGramQuadraticNonnegative' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintFiniteKKTExact.agda
grep -q 'flatGaugeReducedPoincare' DASHI/Physics/YangMills/BalabanSelectedFlatGaugeReducedFloorExact.agda
grep -q 'flatConstantRedundancyNotAutomaticallyTransported' DASHI/Physics/YangMills/BalabanSelectedGaugeRedundancyHolonomyGuardExact.agda
grep -q 'actualFlatGaugeAdjointPointwiseExact' DASHI/Physics/YangMills/BalabanSelectedFlatGaugeAdjointGramFloorExact.agda
grep -q 'actualFlatGaugeGramReducedFloor' DASHI/Physics/YangMills/BalabanSelectedFlatGaugeAdjointGramFloorExact.agda
grep -q 'transposeFrobeniusBound' DASHI/Physics/YangMills/BalabanFiniteRectangularTransposeFrobeniusExact.agda
grep -q 'gaugeAdjointDefectSelectedRadiusBound' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeAdjointDefectExact.agda
grep -q 'perturbedReducedFloor' DASHI/Physics/YangMills/BalabanFiniteReducedFloorPerturbationExact.agda
grep -q 'selectedBackgroundGaugeAdjointReducedFloor' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeReducedFloorExact.agda
grep -q 'selectedBackgroundGaugeReducedFloor = + 29 / 1024' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeReducedFloorExact.agda
grep -q 'regularizedFlatGaugeGreenLeftInverse' DASHI/Physics/YangMills/BalabanSelectedFlatGaugeRegularizedGreenExact.agda
grep -q 'regularizedFlatGaugeGreenRightInverse' DASHI/Physics/YangMills/BalabanSelectedFlatGaugeRegularizedGreenExact.agda
grep -q 'vacuumOrthogonalRecoveryTransfersUniformGap' DASHI/Physics/YangMills/BalabanVacuumOrthogonalMoscoRecoveryExact.agda

grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeReducedFloorExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeReducedFloorExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/YangMills/BalabanFiniteReducedFloorPerturbationExact.agda
grep -q '10.1016/0001-8708(69)90009-7' DASHI/Physics/YangMills/BalabanMoscoRecoveryGapTransferExact.agda
grep -q '10.4310/cag.2003.v11.n4.a1' DASHI/Physics/YangMills/BalabanVacuumOrthogonalMoscoRecoveryExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound42MasterReconciledValidation.agda