#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
  DASHI/Analysis/RiemannReflectionPairBlockExact.agda
  DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
  DASHI/Analysis/RiemannComplexPoissonChannelSplitExact.agda
  DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda
  DASHI/Analysis/RiemannComplexPoissonFiniteRetentionExact.agda
  DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda
  DASHI/Analysis/RiemannMixedChannelAlmostOrthogonalityExact.agda
  DASHI/Analysis/RiemannPrimeSideExcessNormalizationExact.agda
  DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda
  DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda
  DASHI/Analysis/RiemannHermitianExcessDetectabilityAssemblyExact.agda
  DASHI/Analysis/RiemannHermitianPowerAmplificationExact.agda
  DASHI/Analysis/RiemannHermitianLocalizationAmplificationExact.agda
  DASHI/Analysis/RiemannArithmeticUnitarityRigidityBoundary.agda
  DASHI/Analysis/RiemannHermitianEndgameTrichotomyExact.agda
  DASHI/Analysis/RiemannHermitianDreamRouteExact.agda
  DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
  DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
  DASHI/Analysis/ZetaTheoremSurface.agda
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || { echo "missing or empty source: $source" >&2; exit 1; }
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
  grep -F "$2" "$1" >/dev/null || {
    echo "missing required marker '$2' in $1" >&2
    exit 1
  }
}

orbit=DASHI/Analysis/RiemannReflectionOrbitDefectExact.agda
pair=DASHI/Analysis/RiemannReflectionPairBlockExact.agda
hyper=DASHI/Analysis/RiemannWeilOffLineHyperbolicBlockExact.agda
channels=DASHI/Analysis/RiemannComplexPoissonChannelSplitExact.agda
energy=DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda
finite=DASHI/Analysis/RiemannComplexPoissonFiniteRetentionExact.agda
kernel=DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda
mixed=DASHI/Analysis/RiemannMixedChannelAlmostOrthogonalityExact.agda
primeex=DASHI/Analysis/RiemannPrimeSideExcessNormalizationExact.agda
assembly=DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda
detect=DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda
detectassembly=DASHI/Analysis/RiemannHermitianExcessDetectabilityAssemblyExact.agda
power=DASHI/Analysis/RiemannHermitianPowerAmplificationExact.agda
localamp=DASHI/Analysis/RiemannHermitianLocalizationAmplificationExact.agda
rigidity=DASHI/Analysis/RiemannArithmeticUnitarityRigidityBoundary.agda
trichotomy=DASHI/Analysis/RiemannHermitianEndgameTrichotomyExact.agda
dream=DASHI/Analysis/RiemannHermitianDreamRouteExact.agda
c3=DASHI/Analysis/RiemannReflectionC3OrbitShapeBridgeExact.agda
regression=DASHI/Analysis/RiemannReflectionOrbitDefectRegression.agda
surface=DASHI/Analysis/ZetaTheoremSurface.agda
aggregate=DASHI/EverythingRiemannReflectionOrbitDefect2026.agda

require_pattern "$orbit" 'squaredDefectReflectionInvariant'
require_pattern "$pair" 'reflectionBlockDeterminantMagnitudeIsSquaredDefect'
require_pattern "$hyper" 'sourceSignatureCannotDetermineSquaredDefect'
require_pattern "$channels" 'bilinearDiagonalTransverseVanishes'
require_pattern "$channels" 'hermitianDiagonalTransverseDoubles'
require_pattern "$channels" 'bilinearAndHermitianRecoverTwiceFirstTransverse'
require_pattern "$energy" 'pairBlockFrobeniusDecomposition'
require_pattern "$energy" 'holomorphicBaselineCannotDetermineHermitianEnergy'
require_pattern "$finite" 'ComplexPoissonNormContract'
require_pattern "$finite" 'ComplexPoissonStripContinuation'
require_pattern "$finite" 'FiniteGridTailLedger'
require_pattern "$finite" 'FiniteRetentionCertificate'
require_pattern "$kernel" 'holomorphicPlusHermitianSquaresExposePairCrossCore'
require_pattern "$kernel" 'pairCrossCorePlusMixedEnergyIsAlignedEnergy'
require_pattern "$kernel" 'negativeInterferenceCoreIsMinusOne'
require_pattern "$mixed" 'MixedChannelGlobalLedger'
require_pattern "$mixed" 'PairAlmostOrthogonality'
require_pattern "$mixed" 'RetainedPairCertificate'
require_pattern "$mixed" 'AlmostOrthogonalityProducer'
require_pattern "$primeex" 'PrimeSideExcessNormalization'
require_pattern "$primeex" 'rawTraceNeedNotVanishWhenExcessVanishes'
require_pattern "$primeex" 'AlpogeFurmanTraceScaleAdapter'
require_pattern "$assembly" 'finiteZeroForcesTailZero'
require_pattern "$assembly" 'pointwiseTransverseDefectVanishesFromZeroArithmeticBudget'
require_pattern "$detect" 'detectableOffLinePairContradictsGlobalErrorBound'
require_pattern "$detect" 'boundedByNonzeroErrorDoesNotForceVanishing'
require_pattern "$detectassembly" 'HermitianExcessDetectabilityAssembly'
require_pattern "$detectassembly" 'hermitianExcessDetectabilityContradiction'
require_pattern "$detectassembly" 'producerExcludesOffLine'
require_pattern "$power" 'powerGapDecomposition'
require_pattern "$power" 'canonicalPowerAmplificationCertificate'
require_pattern "$power" 'unitGapResidualLevel4'
require_pattern "$localamp" 'LocalizedPairLedger'
require_pattern "$localamp" 'AmplificationDetectabilityLedger'
require_pattern "$localamp" 'HigherMomentLocalizationProducer'
require_pattern "$rigidity" 'ArithmeticRigiditySystem'
require_pattern "$rigidity" 'rigidityClosesTransverseDefect'
require_pattern "$rigidity" 'SatakeAnalogyBoundary'
require_pattern "$trichotomy" 'EndgameAlternative'
require_pattern "$trichotomy" 'endgameAlternativeClosesOffLine'
require_pattern "$dream" 'HermitianProducerStack'
require_pattern "$dream" 'hermitianDreamRouteClosesOffLine'
require_pattern "$dream" 'AlpogeFurmanHermitianDreamProducer'
require_pattern "$c3" 'completePhaseOrbitCancels'
require_pattern "$regression" 'regressionNegativeInterference'
require_pattern "$surface" 'RiemannHermitianExcessDetectabilityAssemblyExact'
require_pattern "$surface" 'RiemannHermitianDreamRouteExact'
require_pattern "$aggregate" 'RiemannComplexPoissonFiniteRetentionExact'
require_pattern "$aggregate" 'RiemannMixedChannelAlmostOrthogonalityExact'
require_pattern "$aggregate" 'RiemannPrimeSideExcessNormalizationExact'
require_pattern "$aggregate" 'RiemannHermitianExcessDetectabilityAssemblyExact'
require_pattern "$aggregate" 'RiemannHermitianLocalizationAmplificationExact'
require_pattern "$aggregate" 'RiemannArithmeticUnitarityRigidityBoundary'
require_pattern "$aggregate" 'RiemannHermitianEndgameTrichotomyExact'
require_pattern "$aggregate" 'RiemannHermitianDreamRouteExact'

DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh \
  DASHI/Analysis/RiemannComplexPoissonChannelSplitExact.agda \
  DASHI/Analysis/RiemannComplexPoissonPairEnergyExact.agda \
  DASHI/Analysis/RiemannComplexPoissonFiniteRetentionExact.agda \
  DASHI/Analysis/RiemannWeilPairKernelFrobeniusExact.agda \
  DASHI/Analysis/RiemannMixedChannelAlmostOrthogonalityExact.agda \
  DASHI/Analysis/RiemannPrimeSideExcessNormalizationExact.agda \
  DASHI/Analysis/RiemannHermitianDefectAssemblyExact.agda \
  DASHI/Analysis/RiemannHermitianDetectabilityGapExact.agda \
  DASHI/Analysis/RiemannHermitianExcessDetectabilityAssemblyExact.agda \
  DASHI/Analysis/RiemannHermitianPowerAmplificationExact.agda \
  DASHI/Analysis/RiemannHermitianLocalizationAmplificationExact.agda \
  DASHI/Analysis/RiemannArithmeticUnitarityRigidityBoundary.agda \
  DASHI/Analysis/RiemannHermitianEndgameTrichotomyExact.agda \
  DASHI/Analysis/RiemannHermitianDreamRouteExact.agda \
  DASHI/EverythingRiemannReflectionOrbitDefect2026.agda
