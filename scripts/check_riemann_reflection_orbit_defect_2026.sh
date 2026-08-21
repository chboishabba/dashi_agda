#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
  DASHI/Analysis/RiemannReflectionPairBlockExact.agda
  DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
  DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda
  DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda
  DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda
  DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda
  DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
  DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
  DASHI/Analysis/ZetaTheoremSurface.agda
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi

  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

orbit=DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
pair=DASHI/Analysis/RiemannReflectionPairBlockExact.agda
hyper=DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
energy=DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda
kernel=DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda
assembly=DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda
detect=DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda
c3=DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
regression=DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
surface=DASHI/Analysis/ZetaTheoremSurface.agda
aggregate=DASHI/EverythingRiemannReflectionOrbitDefect2026.agda

require_pattern "$orbit" 'reflectInvolutive'
require_pattern "$orbit" 'reflectionFixedImpliesCriticalCentre'
require_pattern "$orbit" 'squaredDefectReflectionInvariant'
require_pattern "$orbit" 'zeroDefectImpliesCriticalCentre'
require_pattern "$orbit" 'leftRightCountsEqual'
require_pattern "$orbit" 'nonFixedSplitsIntoEqualSides'
require_pattern "$pair" 'reflectionBlockTraceAlwaysZero'
require_pattern "$pair" 'reflectionBlockDeterminantMagnitudeIsSquaredDefect'
require_pattern "$pair" 'nearAndFarTraceCollide'
require_pattern "$hyper" 'sourcePositiveIndexBudget'
require_pattern "$hyper" 'offLineCountIsTwoSourcePositiveBudgets'
require_pattern "$hyper" 'sourceSignatureCannotDetermineSquaredDefect'
require_pattern "$hyper" 'DistanceSensitiveOffLineAdapter'
require_pattern "$energy" 'fullGridEnergyDecomposition'
require_pattern "$energy" 'pairBlockFrobeniusDecomposition'
require_pattern "$energy" 'holomorphicBaselineCannotDetermineHermitianEnergy'
require_pattern "$energy" 'ComplexPoissonCoercivityAdapter'
require_pattern "$energy" 'FiniteCompressionTransferAdapter'
require_pattern "$energy" 'HermitianArithmeticTransportAdapter'
require_pattern "$kernel" 'holomorphicPlusHermitianSquaresExposePairCrossCore'
require_pattern "$kernel" 'pairCrossCorePlusMixedEnergyIsAlignedEnergy'
require_pattern "$kernel" 'holomorphicHermitianPlusTwiceMixedIsTwiceAligned'
require_pattern "$kernel" 'diagonalKernelEnergyIdentity'
require_pattern "$kernel" 'negativeInterferenceCoreIsMinusOne'
require_pattern "$kernel" 'PairKernelInterferenceAdapter'
require_pattern "$assembly" 'finiteRetentionDominationIdentity'
require_pattern "$assembly" 'finiteZeroForcesTailZero'
require_pattern "$assembly" 'zeroArithmeticBudgetForcesWeightedDefectZero'
require_pattern "$assembly" 'pointwiseTransverseDefectVanishesFromZeroArithmeticBudget'
require_pattern "$detect" 'detectableOffLinePairContradictsGlobalErrorBound'
require_pattern "$detect" 'boundedByNonzeroErrorDoesNotForceVanishing'
require_pattern "$detect" 'RHDetectabilityProducer'
require_pattern "$c3" 'completePhaseOrbitCancels'
require_pattern "$c3" 'c3OrbitRoleInversionInvariant'
require_pattern "$c3" 'zetaSameRoleCanRetainDifferentDefects'
require_pattern "$regression" 'regressionSignatureCannotRecoverDefect'
require_pattern "$regression" 'regressionHolomorphicBaselineCannotRecoverHermitian'
require_pattern "$regression" 'regressionPairKernelIdentity'
require_pattern "$regression" 'regressionNegativeInterference'
require_pattern "$surface" 'RiemannComplexPoissonPairEnergyExact'
require_pattern "$surface" 'RiemannWeilPairKernelFrobeniusExact'
require_pattern "$aggregate" 'RiemannHermitianDefectAssemblyExact'
require_pattern "$aggregate" 'RiemannHermitianDetectabilityGapExact'

DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda \
  DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda \
  DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda \
  DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda \
  DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda \
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
