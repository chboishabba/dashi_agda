#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_riemann_reflection_orbit_defect_2026.sh

sources=(
  DASHI/Analysis/PoleQuotientedExteriorDeskTestExact.agda
  DASHI/Analysis/PoleRankTwoQuotientedExteriorDeskTestExact.agda
  DASHI/Analysis/RiemannG21TwoByTwoMixedObstructionExact.agda
  DASHI/Analysis/RiemannG21AugmentedDeterminantFiniteExact.agda
  DASHI/Analysis/RiemannG21LiteralPoleRankAuditExact.agda
  DASHI/Analysis/RiemannG21PoleMainModeSeparationExact.agda
  DASHI/Analysis/RiemannG21ActualZetaHeightSeparationBoundary.agda
  DASHI/Analysis/RiemannG21ConjugateHeightSourceBridgeExact.agda
  DASHI/Analysis/RiemannG21SymmetricSampleBlockReductionExact.agda
  DASHI/Analysis/RiemannG21HyperbolicWeightMonotonicityTargetExact.agda
  DASHI/Analysis/RiemannG21ScaledHyperbolicMonotonicityBridgeExact.agda
  DASHI/Analysis/RiemannG21EvenHyperbolicAlgebraicRouteExact.agda
  DASHI/Analysis/RiemannG21MathlibHyperbolicReceiptBoundary.agda
  DASHI/Analysis/StrictKernelMomentRatioExact.agda
  DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda
  DASHI/Analysis/RiemannG21TwoHeightMomentRatioTargetExact.agda
  DASHI/Analysis/RiemannG21TwoPointCovarianceShadowExact.agda
  DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda
  DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda
  DASHI/Analysis/RiemannG21ContextualAlternativeNonpromotionExact.agda
  DASHI/Analysis/RiemannG21ContextualAlternativeFiniteInstanceExact.agda
  DASHI/Analysis/RiemannG21OffLinePoleQuotientTransversalityExact.agda
  DASHI/Analysis/RiemannG21PrimePairKernelExact.agda
  DASHI/Analysis/RiemannG21PoleQuotientedExteriorExact.agda
  DASHI/Analysis/RiemannG21CrossPollinationExact.agda
  DASHI/Analysis/RiemannG21Regression.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || { echo "missing or empty source: $source" >&2; exit 1; }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK' "$source"; then
    echo "forbidden trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  grep -F "$2" "$1" >/dev/null || {
    echo "missing required marker '$2' in $1" >&2
    exit 1
  }
}

require_pattern DASHI/Analysis/RiemannG21TwoByTwoMixedObstructionExact.agda 'rankOnePoleDoesNotKillMixedTwoByTwoDeterminant'
require_pattern DASHI/Analysis/RiemannG21AugmentedDeterminantFiniteExact.agda 'augmentedPoleQuotientPreservesSignedDeterminant'
require_pattern DASHI/Analysis/RiemannG21LiteralPoleRankAuditExact.agda 'genericTwoPoleFourSampleCase'
require_pattern DASHI/Analysis/RiemannG21PoleMainModeSeparationExact.agda 'MainModeTransportBridge'
require_pattern DASHI/Analysis/RiemannG21ActualZetaHeightSeparationBoundary.agda 'offLineHeightCannotReachPoleHeightForActualZetaIsTrue'
require_pattern DASHI/Analysis/RiemannG21ConjugateHeightSourceBridgeExact.agda 'TwoHeightExteriorTarget'
require_pattern DASHI/Analysis/RiemannG21SymmetricSampleBlockReductionExact.agda 'SymmetricSampleTwoHeightAdmission'
require_pattern DASHI/Analysis/RiemannG21SymmetricSampleBlockReductionExact.agda 'evenOnlyOddMinorFails'
require_pattern DASHI/Analysis/RiemannG21EvenHyperbolicAlgebraicRouteExact.agda 'evenSectorIndependentOfXTanhRouteIsTrue'
require_pattern DASHI/Analysis/RiemannG21MathlibHyperbolicReceiptBoundary.agda 'Real.self_lt_sinh_iff'
require_pattern DASHI/Analysis/RiemannG21MathlibHyperbolicReceiptBoundary.agda 'leanProofTermImportedIntoAgdaIsFalse'
require_pattern DASHI/Analysis/StrictKernelMomentRatioExact.agda 'tp2MinorPositive'
require_pattern DASHI/Analysis/StrictKernelMomentRatioExact.agda 'finiteTP2MinorDistinct'
require_pattern DASHI/Analysis/StrictKernelMomentRatioExact.agda 'finiteMomentCrossProductStrictlySeparated'
require_pattern DASHI/Analysis/StrictKernelMomentRatioExact.agda 'continuumStrictCompositionDerivedInAgdaIsFalse'
require_pattern DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda 'sinhTP2MinorPositive'
require_pattern DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda 'positiveMargin'
require_pattern DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda 'oddMomentDeterminantStrictNegative'
require_pattern DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda 'symmetrizedDoubleIntegralIdentity'
require_pattern DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda 'continuumOddMomentStrictSignDerivedIsFalse'
require_pattern DASHI/Analysis/RiemannG21TwoPointCovarianceShadowExact.agda 'twoPointMomentCrossProductDecomposition'
require_pattern DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda 'directDeterminantErrorBelowMargin'
require_pattern DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda 'finiteRadiusSignPreserved'
require_pattern DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda 'entrywiseTriangleBoundRequiredByInterfaceIsFalse'
require_pattern DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda 'strictSinhTP2'
require_pattern DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda 'oddMomentDeterminantStrictSign'
require_pattern DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda 'directDeterminantMarginTransfer'
require_pattern DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda 'finiteRadiusParityMinors'
require_pattern DASHI/Analysis/RiemannG21ContextualAlternativeNonpromotionExact.agda '10.1038/s41467-026-69034-7'
require_pattern DASHI/Analysis/RiemannG21ContextualAlternativeNonpromotionExact.agda 'paperProvesRiemannHypothesisIsFalse'
require_pattern DASHI/Analysis/RiemannG21ContextualAlternativeFiniteInstanceExact.agda 'canonicalContextualAlternativeDescription'
require_pattern DASHI/Analysis/RiemannG21OffLinePoleQuotientTransversalityExact.agda 'OffLinePoleQuotientTransversality'
require_pattern DASHI/Analysis/RiemannG21PrimePairKernelExact.agda 'RectangleNonseparabilityWitness'
require_pattern DASHI/Analysis/RiemannG21PrimePairKernelExact.agda 'RankOneMinorObstruction'
require_pattern DASHI/Analysis/RiemannG21PoleQuotientedExteriorExact.agda 'strictSinhTP2OddKernel'
require_pattern DASHI/Analysis/RiemannG21PoleQuotientedExteriorExact.agda 'strictOddMomentDeterminant'
require_pattern DASHI/Analysis/RiemannG21PoleQuotientedExteriorExact.agda 'directDeterminantMarginTransfer'
require_pattern DASHI/Analysis/RiemannG21PoleQuotientedExteriorExact.agda 'riemannHypothesisDerivedIsFalse'

DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/RiemannG21Regression.agda \
  DASHI/Analysis/RiemannG21ParityMinorAnalyticFrontierExact.agda \
  DASHI/Analysis/StrictKernelMomentRatioExact.agda \
  DASHI/Analysis/RiemannG21OddSinhTP2Exact.agda \
  DASHI/Analysis/RiemannG21DeterminantMarginTransferExact.agda \
  DASHI/Analysis/RiemannG21ContextualAlternativeFiniteInstanceExact.agda
