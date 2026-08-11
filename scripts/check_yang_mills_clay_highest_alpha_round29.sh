#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round28.sh

files=(
  DASHI/Physics/YangMills/BalabanP33PlaquetteLinearClosureScalingExact.agda
  DASHI/Physics/YangMills/BalabanP33PlaquetteLinearCurlIdentificationExact.agda
  DASHI/Physics/YangMills/BalabanP33SelectedCorrelationToWLocalExact.agda
  DASHI/Physics/YangMills/BalabanP33QuadraticPolarizationTwoCoordinateExact.agda
  DASHI/Physics/YangMills/BalabanP33SymmetricTwoByTwoInverseExact.agda
  DASHI/Physics/YangMills/BalabanP33StrictDiscountedMarginFactorizationExact.agda
  DASHI/Physics/YangMills/YangMillsClaimAuthoritySubmissionSequenceExact.agda
  DASHI/Physics/YangMills/YangMillsHighestAlphaGateDependencyExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound29UnifiedGateValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

test -f DASHI/Physics/YangMills/BalabanClayHighestAlphaRound28UniformityRoutesValidation.agda

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round twenty nine contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'BalabanP33PlaquetteLinearClosureScalingExact.agda:plaquetteExpansionExact'
  'BalabanP33PlaquetteLinearClosureScalingExact.agda:scaledPlaquetteExpansionExact'
  'BalabanP33PlaquetteLinearClosureScalingExact.agda:linearClosureRemovesFirstOrder'
  'BalabanP33PlaquetteLinearClosureScalingExact.agda:unbalancedSingleLinkDefectExact'
  'BalabanP33PlaquetteLinearClosureScalingExact.agda:balancedOppositeLinkDefectExact'
  'BalabanP33PlaquetteLinearCurlIdentificationExact.agda:plaquetteLinearEqualsDiscreteCurl'
  'BalabanP33PlaquetteLinearCurlIdentificationExact.agda:curvatureLowerTransfersToPlaquetteLinear'
  'BalabanP33PlaquetteLinearCurlIdentificationExact.agda:exactGradientHasZeroDiscreteCurl'
  'BalabanP33PlaquetteLinearCurlIdentificationExact.agda:exactGradientHasZeroPlaquetteLinearTerm'
  'BalabanP33SelectedCorrelationToWLocalExact.agda:negativeBudgetSumExact'
  'BalabanP33SelectedCorrelationToWLocalExact.agda:correlatedControlTransfersLowerBound'
  'BalabanP33SelectedCorrelationToWLocalExact.agda:closedDefectEqualsRemainder'
  'BalabanP33SelectedCorrelationToWLocalExact.agda:correlatedCancellationTransfersLowerBound'
  'BalabanP33SelectedCorrelationToWLocalExact.agda:physicalInputsImplyWLocalScalar'
  'BalabanP33QuadraticPolarizationTwoCoordinateExact.agda:polarizationExact'
  'BalabanP33QuadraticPolarizationTwoCoordinateExact.agda:offDiagonalRecoveredByQuadraticDifference'
  'BalabanP33SymmetricTwoByTwoInverseExact.agda:leftInverse00'
  'BalabanP33SymmetricTwoByTwoInverseExact.agda:leftInverse11'
  'BalabanP33SymmetricTwoByTwoInverseExact.agda:rightInverse00'
  'BalabanP33SymmetricTwoByTwoInverseExact.agda:rightInverse11'
  'BalabanP33StrictDiscountedMarginFactorizationExact.agda:strictMarginFactorization'
  'BalabanP33StrictDiscountedMarginFactorizationExact.agda:thirtyTwoScaledBudgetGap'
  'YangMillsClaimAuthoritySubmissionSequenceExact.agda:selfHostedClaimDoesNotAdvanceToQualifyingOutlet'
  'YangMillsClaimAuthoritySubmissionSequenceExact.agda:machineArtifactDoesNotAdvanceToQualifyingOutlet'
  'YangMillsHighestAlphaGateDependencyExact.agda:finitePropagatorIsNotClayCompletion'
  'YangMillsHighestAlphaGateDependencyExact.agda:uniformRGIsNotContinuumOS'
  'YangMillsHighestAlphaGateDependencyExact.agda:continuumOSIsNotMassGap'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Physics/YangMills/$file"
done

grep -q '10.1007/BF01229381' DASHI/Physics/YangMills/BalabanP33PlaquetteLinearClosureScalingExact.agda
grep -q '10.1007/BF01466594' DASHI/Physics/YangMills/BalabanP33PlaquetteLinearCurlIdentificationExact.agda
grep -q '10.1103/PhysRevD.10.2445' DASHI/Physics/YangMills/BalabanP33SelectedCorrelationToWLocalExact.agda
grep -q '10.1017/CBO9781139020411' DASHI/Physics/YangMills/BalabanP33QuadraticPolarizationTwoCoordinateExact.agda
grep -q '10.1007/BF01646473' DASHI/Physics/YangMills/BalabanP33SymmetricTwoByTwoInverseExact.agda
grep -q '10.1007/s00023-013-0303-3' DASHI/Physics/YangMills/BalabanP33StrictDiscountedMarginFactorizationExact.agda
grep -q 'Rules for the Millennium Prize Problems' DASHI/Physics/YangMills/YangMillsClaimAuthoritySubmissionSequenceExact.agda
grep -q '10.1007/BF01608978' DASHI/Physics/YangMills/YangMillsHighestAlphaGateDependencyExact.agda

grep -q 'physical SU(2) theorem must prove' DASHI/Physics/YangMills/BalabanP33PlaquetteLinearClosureScalingExact.agda
grep -q 'discrete-Stokes identity is fully proved' DASHI/Physics/YangMills/BalabanP33PlaquetteLinearCurlIdentificationExact.agda
grep -q 'does not fabricate' DASHI/Physics/YangMills/BalabanP33SelectedCorrelationToWLocalExact.agda
grep -q 'physical 3072-coordinate inverse' DASHI/Physics/YangMills/BalabanP33SymmetricTwoByTwoInverseExact.agda
grep -q 'No canonical inhabitant' DASHI/Physics/YangMills/YangMillsHighestAlphaGateDependencyExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound29UnifiedGateValidation.agda
