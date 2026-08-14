#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

BASE_CHECKER="scripts/check_dynamic_biology_round21.sh"
if [[ -f "$BASE_CHECKER" ]]; then
  bash "$BASE_CHECKER"
fi

FILES=(
  DASHI/Biology/Physical/FiniteStochasticReactionCommittorExact.agda
  DASHI/Biology/Physical/FiniteChemicalMasterGeneratorExact.agda
  DASHI/Biology/Physical/FiniteFluctuationRelationExact.agda
  DASHI/Biology/Physical/CommittorConsumerFutureStatisticExact.agda
  DASHI/Biology/Physical/FiniteElectrodiffusiveMovingBoundaryExact.agda
  DASHI/Biology/Physical/FinitePNPFreeEnergyDissipationExact.agda
  DASHI/Biology/Physical/FiniteMorphogeneticBasinControlExact.agda
  DASHI/Biology/Physical/PlanarianControlCalibrationExact.agda
  DASHI/Biology/Physical/BDNACalibratedHelicalGeometryExact.agda
  DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda
  DASHI/Biology/Physical/C3CubeCyclotomicParsevalExact.agda
  DASHI/Biology/Physical/C3DirectGroupConvolutionExact.agda
  DASHI/Biology/Physical/C3CubeDirectGroupConvolutionExact.agda
  DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda
  DASHI/Cognition/PNF/TaskActionRepresentationGeometryExact.agda
  DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda
  DASHI/Cognition/PNF/FinitePathTransitionOptimalityExact.agda
  DASHI/Cognition/PNF/WaveGrayLocalGlobalGeometryExact.agda
  DASHI/Cognition/PNF/FutureGeometryEmbeddingExact.agda
  DASHI/Cognition/PNF/RateFutureTransitionParetoExact.agda
  DASHI/Cognition/PNF/GenericExpectedFibreRateExact.agda
  DASHI/Cognition/PNF/DynamicMultimodalTransitionGeometryExact.agda
  DASHI/Cognition/PNF/CacheUpdateReopenGeometryExact.agda
  DASHI/Cognition/PNF/StableProbabilisticObservationFutureBridgeExact.agda
  DASHI/Foundations/CantorFiniteClopenPremeasureExact.agda
  DASHI/EverythingQuantitativeFutureGeometryRound22.agda
)

for f in "${FILES[@]}"; do
  test -s "$f"

  # Scan source lines (not ordinary -- comments) for explicit trust escapes or
  # unsolved holes.  This intentionally avoids rejecting mathematical prose
  # containing words such as "unsafe" or punctuation such as question marks.
  if grep -vE '^[[:space:]]*--' "$f" \
      | grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!!\}|--allow-unsolved-metas|primTrustMe'; then
    echo "fail-closed scan rejected $f" >&2
    exit 1
  fi
done

# Stochastic chemistry / committor.
grep -q 'committorHarmonic' DASHI/Biology/Physical/FiniteStochasticReactionCommittorExact.agda
grep -q 'generatorCommittorHarmonic' DASHI/Biology/Physical/FiniteChemicalMasterGeneratorExact.agda
grep -q 'multiplicativeFluctuationRelation' DASHI/Biology/Physical/FiniteFluctuationRelationExact.agda
grep -q 'sameTargetLawDoesNotDetermineHistory' DASHI/Biology/Physical/CommittorConsumerFutureStatisticExact.agda

# Electrodiffusion / active energy / basin calibration.
grep -q 'transportConservesAmount' DASHI/Biology/Physical/FiniteElectrodiffusiveMovingBoundaryExact.agda
grep -q 'passiveDissipationLowersStoredEnergy' DASHI/Biology/Physical/FiniteElectrodiffusiveMovingBoundaryExact.agda
grep -q 'passiveTransportLowersFreeEnergy' DASHI/Biology/Physical/FinitePNPFreeEnergyDissipationExact.agda
grep -q 'strongPulseIsOneStepCostOptimal' DASHI/Biology/Physical/FiniteMorphogeneticBasinControlExact.agda
grep -q 'parameterSweepSuccessfulCount' DASHI/Biology/Physical/PlanarianControlCalibrationExact.agda
grep -q 'idealRiseTimesTurnIsPitch' DASHI/Biology/Physical/BDNACalibratedHelicalGeometryExact.agda
grep -q 'idealTwistTimesTurnIsFullRotation' DASHI/Biology/Physical/BDNACalibratedHelicalGeometryExact.agda

# Exact cyclotomic Fourier closure.
grep -q 'cubeCharacterOrthogonality' DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda
grep -q 'cubeFourierInversion' DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda
grep -q 'cubeFourierForwardInverse' DASHI/Biology/Physical/C3CubeCyclotomicFourierExact.agda
grep -q 'cubeParsevalNormalised' DASHI/Biology/Physical/C3CubeCyclotomicParsevalExact.agda
grep -q 'c3DirectConvolutionTheorem' DASHI/Biology/Physical/C3DirectGroupConvolutionExact.agda
grep -q 'c3CubeDirectConvolutionTheorem' DASHI/Biology/Physical/C3CubeDirectGroupConvolutionExact.agda
grep -q 'directEqualsSpectralConvolution' DASHI/Biology/Physical/C3CubeDirectGroupConvolutionExact.agda
grep -q 'phaseTripleSixRoundTrip' DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda
grep -q 'sameCircularProjectionDifferentHistory' DASHI/Biology/Physical/Harmonic369HelixLiftExact.agda

# Task action / grokking / representation geometry.
grep -q 'c3ActionBecomesCyclotomicMultiplication' DASHI/Cognition/PNF/TaskActionRepresentationGeometryExact.agda
grep -q 'algorithmicPairLinearises' DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda
grep -q 'heldOutCyclotomicFactorization' DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda
grep -q 'unitDistancePathIsOptimal' DASHI/Cognition/PNF/FinitePathTransitionOptimalityExact.agda
grep -q 'waveLocalGlobalSeparation' DASHI/Cognition/PNF/WaveGrayLocalGlobalGeometryExact.agda
grep -q 'composeLipschitz' DASHI/Cognition/PNF/FutureGeometryEmbeddingExact.agda
grep -q 'waveGrayTransitionOptimalAtZero' DASHI/Cognition/PNF/RateFutureTransitionParetoExact.agda

# Expected local rate / multimodal / runtime / probabilistic quotient.
grep -q 'normalizedConstantRateIsRate' DASHI/Cognition/PNF/GenericExpectedFibreRateExact.agda
grep -q 'orientedZeroNormalizedExpectedRate' DASHI/Cognition/PNF/GenericExpectedFibreRateExact.agda
grep -q 'finiteTraceNonExpansive' DASHI/Cognition/PNF/DynamicMultimodalTransitionGeometryExact.agda
grep -q 'crossModalUpdateGeometryBound' DASHI/Cognition/PNF/DynamicMultimodalTransitionGeometryExact.agda
grep -q 'localDeltaOperationallyBetter' DASHI/Cognition/PNF/CacheUpdateReopenGeometryExact.agda
grep -q 'stableProbabilisticPairIsFutureEquivalent' DASHI/Cognition/PNF/StableProbabilisticObservationFutureBridgeExact.agda
grep -q 'stableProbabilityPartitionIsFutureSafe' DASHI/Cognition/PNF/StableProbabilisticObservationFutureBridgeExact.agda

# Cantor finite clopen algebra/premeasure.
grep -q 'clopenMassComplement' DASHI/Foundations/CantorFiniteClopenPremeasureExact.agda
grep -q 'clopenFiniteAdditivity' DASHI/Foundations/CantorFiniteClopenPremeasureExact.agda
grep -q 'refinementPreservesMass' DASHI/Foundations/CantorFiniteClopenPremeasureExact.agda
grep -q 'refinementCommutesWithUnion' DASHI/Foundations/CantorFiniteClopenPremeasureExact.agda

# Source metadata pinned in theorem-bearing files.
grep -q '10.1021/j100540a008' DASHI/Biology/Physical/FiniteChemicalMasterGeneratorExact.agda
grep -q '10.1113/jphysiol.1952.sp004764' DASHI/Biology/Physical/FiniteElectrodiffusiveMovingBoundaryExact.agda
grep -q '10.1098/rstb.1952.0012' DASHI/Biology/Physical/FiniteElectrodiffusiveMovingBoundaryExact.agda
grep -q '10.1089/bioe.2021.0036' DASHI/Biology/Physical/PlanarianControlCalibrationExact.agda
grep -q '10.1006/jmbi.2001.4987' DASHI/Biology/Physical/BDNACalibratedHelicalGeometryExact.agda
grep -q '10.1093/nar/gkw133' DASHI/Biology/Physical/BDNACalibratedHelicalGeometryExact.agda
grep -q 'arXiv:2301.05217' DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda
grep -q 'arXiv:2301.02679' DASHI/Cognition/PNF/CyclotomicGrokkingActionLinearizationExact.agda

if command -v agda >/dev/null 2>&1; then
  agda -i . -i src DASHI/EverythingQuantitativeFutureGeometryRound22.agda
else
  echo "agda unavailable: structural/fail-closed round-22 scan completed; no kernel-clean claim"
fi
