#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round30.sh

files=(
  DASHI/Physics/YangMills/BalabanStrongCouplingGroupRicciConstantsExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingSUFormulaReconciliationExact.agda
  DASHI/Physics/YangMills/BalabanStrongCouplingWeightedWassersteinRateExact.agda
  DASHI/Physics/YangMills/YangMillsAllBetaMultiscaleLSIAuditExact.agda
  DASHI/Physics/YangMills/YangMillsLatticeGapScaleCompatibilityExact.agda
  DASHI/Physics/YangMills/YangMillsAllBetaExponentialRunningCouplingExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound31GroupRatesAllBetaAuditValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round thirty one contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanStrongCouplingGroupRicciConstantsExact.agda:orthogonalRicciSimplified'
  'BalabanStrongCouplingGroupRicciConstantsExact.agda:specialUnitaryRicciSimplified'
  'BalabanStrongCouplingGroupRicciConstantsExact.agda:specialUnitaryThresholdSaturates'
  'BalabanStrongCouplingGroupRicciConstantsExact.agda:orthogonalThreeThresholdSaturates'
  'BalabanStrongCouplingGroupRicciConstantsExact.agda:configuredSU2SusceptibilityCoefficientExact'
  'BalabanStrongCouplingSUFormulaReconciliationExact.agda:suRicciConstantMatchesOldPerRank'
  'BalabanStrongCouplingSUFormulaReconciliationExact.agda:suFourDimensionalRateMatchesOldNormalization'
  'BalabanStrongCouplingWeightedWassersteinRateExact.agda:weightedRateIsBakryRateMinusWeightLoss'
  'BalabanStrongCouplingWeightedWassersteinRateExact.agda:canonicalWeightedRateIsHalfBakry'
  'BalabanStrongCouplingWeightedWassersteinRateExact.agda:positiveBakryRateChoosesPositiveWeight'
  'BalabanStrongCouplingWeightedWassersteinRateExact.agda:configuredSU2WeightedContractionRateExact'
  'YangMillsAllBetaMultiscaleLSIAuditExact.agda:allBetaDepositIsOnlySketchAuthority'
  'YangMillsAllBetaMultiscaleLSIAuditExact.agda:acceptedInputCannotEqualForbiddenTarget'
  'YangMillsAllBetaMultiscaleLSIAuditExact.agda:fixedBetaGapIsNotScaleCompatibility'
  'YangMillsLatticeGapScaleCompatibilityExact.agda:powProduct'
  'YangMillsLatticeGapScaleCompatibilityExact.agda:quadraticGapIsSpacingSquared'
  'YangMillsLatticeGapScaleCompatibilityExact.agda:quadraticGapRescalesToSpacing'
  'YangMillsAllBetaExponentialRunningCouplingExact.agda:matchedPhysicalGapLowerExact'
  'YangMillsAllBetaExponentialRunningCouplingExact.agda:quadraticPhysicalGapLowerExact'
  'YangMillsAllBetaExponentialRunningCouplingExact.agda:configuredMatchedPhysicalGapExact'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/s00220-022-04609-1' DASHI/Physics/YangMills/BalabanStrongCouplingGroupRicciConstantsExact.agda
grep -q '10.4171/OWR/2022/27' DASHI/Physics/YangMills/YangMillsAllBetaMultiscaleLSIAuditExact.agda
grep -q '10.5281/zenodo.19699784' DASHI/Physics/YangMills/YangMillsAllBetaMultiscaleLSIAuditExact.agda
grep -q 'No canonical inhabitant' DASHI/Physics/YangMills/YangMillsAllBetaMultiscaleLSIAuditExact.agda
grep -q 'No canonical inhabitant' DASHI/Physics/YangMills/YangMillsAllBetaExponentialRunningCouplingExact.agda
grep -q 'K~_S(s^2)' DASHI/Physics/YangMills/BalabanStrongCouplingWeightedWassersteinRateExact.agda
grep -q 'm_\* a <= Delta_latt' DASHI/Physics/YangMills/YangMillsLatticeGapScaleCompatibilityExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound31GroupRatesAllBetaAuditValidation.agda
