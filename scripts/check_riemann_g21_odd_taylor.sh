#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_riemann_g21_pole_quotient.sh

sources=(
  DASHI/Analysis/StrictKernelMomentRatioTwoSupportExact.agda
  DASHI/Analysis/RiemannG21OddTaylorDeterminantExact.agda
  DASHI/Analysis/RiemannG21OddTaylorRemainderDeterminantExact.agda
  DASHI/Analysis/RiemannG21OddTaylorOrderBudgetExact.agda
  DASHI/Analysis/RiemannG21OddTaylorSourceBudgetBoundary.agda
  DASHI/Analysis/RiemannG21OddTaylorDeterminantConstantExact.agda
  DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda
  DASHI/Analysis/RiemannG21OddTaylorRegression.agda
  DASHI/Analysis/RiemannG21StrictTP2TrancheReceipt.agda
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

require_pattern DASHI/Analysis/StrictKernelMomentRatioTwoSupportExact.agda 'twoSupportTP2MomentIdentity'
require_pattern DASHI/Analysis/StrictKernelMomentRatioTwoSupportExact.agda 'oddTwoSupportCompositionIdentity'
require_pattern DASHI/Analysis/RiemannG21OddTaylorDeterminantExact.agda 'oddCubicDeterminantDoubleRadius'
require_pattern DASHI/Analysis/RiemannG21OddTaylorDeterminantExact.agda 'doubleRadiusSignalCoefficientDerivedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorRemainderDeterminantExact.agda 'oddDeterminantErrorIdentity'
require_pattern DASHI/Analysis/RiemannG21OddTaylorRemainderDeterminantExact.agda 'exactSixTermDeterminantErrorDerivedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorOrderBudgetExact.agda 'relativeErrorDegreeGapIsTwo'
require_pattern DASHI/Analysis/RiemannG21OddTaylorSourceBudgetBoundary.agda 'Zeta23.Taper.phi_support_subset'
require_pattern DASHI/Analysis/RiemannG21OddTaylorSourceBudgetBoundary.agda 'fifthOrderSineRemainderLocatedOrDerivedIsFalse'
require_pattern DASHI/Analysis/RiemannG21OddTaylorDeterminantConstantExact.agda 'determinantErrorConstantQ'
require_pattern DASHI/Analysis/RiemannG21OddTaylorDeterminantConstantExact.agda 'explicitRationalCoefficientConstructedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda 'doubleRadiusCoefficient36DerivedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda 'relativeErrorDegreeGapTwoDerivedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda 'explicitDeterminantErrorCoefficientConstructedIsTrue'
require_pattern DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda 'determinantR6InequalityDerivedIsFalse'
require_pattern DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda 'finiteOddMinorSignDerivedIsFalse'

DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/StrictKernelMomentRatioTwoSupportExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorDeterminantExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorRemainderDeterminantExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorOrderBudgetExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorSourceBudgetBoundary.agda \
  DASHI/Analysis/RiemannG21OddTaylorDeterminantConstantExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorQuantitativeFrontierExact.agda \
  DASHI/Analysis/RiemannG21OddTaylorRegression.agda
