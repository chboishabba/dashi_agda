#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

# Retain every prior Round-42 guard first.
bash scripts/check_yang_mills_clay_highest_alpha_round42.sh

files=(
  DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
  DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
  DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round 42 extension contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

grep -q 'transposeProductColumnMassBound' DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
grep -q 'selectedGaugeGramPerturbationAbsoluteColumnMassBound' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
grep -q 'selectedBackgroundFlatGreenPerturbationColumnOneTenthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
grep -q 'applyKernelL1Bound' DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
grep -q 'selectedBackgroundResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedGreenPerturbationColumnOneSixthContraction' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda
grep -q 'selectedBackgroundWeightedResidualPowerL1Decay' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda

grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteRectangularAbsoluteColumnMassExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundGaugeGramPerturbationTwoSidedMassExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundFlatGreenPerturbationTwoSidedContractionExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanFiniteMatrixL1ContractionExact.agda
grep -q '10.1007/978-3-642-66282-9' DASHI/Physics/YangMills/BalabanSelectedBackgroundResidualPowerDecayExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanSelectedBackgroundRationalWeightedPowerDecayExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound42MasterReconciledValidation.agda
