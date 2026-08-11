#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

# Retain every prior Round-42 guard first.
bash scripts/check_yang_mills_clay_highest_alpha_round42.sh

files=(
  DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
  DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
  DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRationalInjectiveInverseExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugePerturbationActionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualActionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
  DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
  DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
  DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|functionExtensionality|funext' "${files[@]}"; then
  echo "round 42 extension contains a hole, postulate, unsafe escape, trust primitive, or extensionality shortcut" >&2
  exit 1
fi

grep -q 'applyComposeRectangularExact' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q 'rectangularAdjointExact' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q 'transposeProductColumnMassBound' DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
grep -q 'selectedGaugeGramPerturbationAbsoluteColumnMassBound' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
grep -q 'selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
grep -q 'applyKernelL1Bound' DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
grep -q 'selectedBackgroundResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q 'oneSixthReopeningBound' DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
grep -q 'oneSixthHomogeneousReopeningPointwiseZero' DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
grep -q 'selectedBackgroundResidualIdentityPlusInjective' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
grep -q 'selectedBackgroundWeightedResidualReopeningSixFifths' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
grep -q 'finiteSquareInjectiveImpliesRationalInverse' DASHI/Physics/YangMills/BalabanFiniteRationalInjectiveInverseExact.agda
grep -q 'selectedResidualIdentityPlusMatrixInjective' DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
grep -q 'selectedWeightedResidualInverseSixFifths' DASHI/Physics/YangMills/BalabanSelectedBackgroundFiniteRationalReopeningExact.agda
grep -q 'selectedGaugeGramPerturbationActsAsExplicitEA' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugePerturbationActionExact.agda
grep -q 'selectedResidualActsAsExplicitFlatGreenEA' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualActionExact.agda
grep -q 'flatGreenBackgroundFactorizationAsMatrix' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'selectedBackgroundGaugeGreenLeftInverse' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'selectedBackgroundGaugeGreenRightInverse' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q 'tiltedGreenColumnL1BelowThree' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
grep -q 'selectedBackgroundGaugeGreenExponentialDecay' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
grep -q 'rootedGaugeOrbitLift' DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
grep -q 'rootedGaugeRepresentativeUniqueInBasedOrbit' DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
grep -q 'selectedPhysicalTangentProjectorInKernel' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
grep -q 'selectedPhysicalTangentProjectorIdempotent' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
grep -q 'rawFlatRedundancyGramZero' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
grep -q 'rawCombinedFlatGramHasNoTwoSidedInverse' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
grep -q 'selectedFlatRawCombinedGramInverseImpossible' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
grep -q 'selectedReducedOrBasedProjectorStillRequiredLevel = conditional' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
grep -q 'finiteRGObservableExpectationPreserved' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda
grep -q 'finiteRGCompositeExpectationPreserved' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda

grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteRectangularRationalExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/YangMills/BalabanFiniteStrictContractionReopeningExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualReopeningExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteRationalInjectiveInverseExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugePerturbationActionExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualActionExact.agda
grep -q '10.1007/BF01240355' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenFiniteExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGreenDecayExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanBasedPathGaugeSectionExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintRawGramNoGoExact.agda
grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanSelectedCombinedConstraintTangentProjectorBoundaryExact.agda
grep -q 'math-ph/0505008' DASHI/Physics/YangMills/BalabanFiniteRGObservableReopeningExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound42MasterReconciledValidation.agda
