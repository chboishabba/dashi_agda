#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round9_moonshine_modular_orbifold.sh

files=(
  DASHI/Biology/BalancedTernaryFourierModeExact.agda
  DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda
  DASHI/Biology/QuaternionSymmetryResolvedWaveExact.agda
  DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda
  DASHI/Biology/ConsciousAccessWaveControlBridgeExact.agda
  DASHI/Biology/ConsciousAccessWaveSourceRegistry.agda
  DASHI/Biology/MonsterWaveModeSeparatingProbeExact.agda
  DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda
  DASHI/Biology/ConsciousAccessRound10WaveSymmetryValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round ten contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Biology/BalancedTernaryFourierModeExact.agda:firstTranslationEigen'
  'DASHI/Biology/BalancedTernaryFourierModeExact.agda:secondTranslationEigen'
  'DASHI/Biology/BalancedTernaryFourierModeExact.agda:canonicalModeCountIsNine'
  'DASHI/Biology/BalancedTernaryFourierModeExact.agda:ordinarySymmetryResolvedDimensionIsThreePowerEleven'
  'DASHI/Biology/BalancedTernaryFourierModeExact.agda:completionReadoutFirstInvariant'
  'DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda:radialSourceCenterDivergenceFour'
  'DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda:rotationalCenterCurlFour'
  'DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda:spiralCenterCurlFour'
  'DASHI/Biology/QuaternionSymmetryResolvedWaveExact.agda:observeModuloOrientationInvariant'
  'DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda:sameStructureDifferentFieldChangesEffectiveTopology'
  'DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda:firstPullbackMovesStencilToMinusFirst'
  'DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda:oppositePhaseSuperpositionCancels'
  'DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda:fieldChangeCanChangeFutureNeuralState'
  'DASHI/Biology/ConsciousAccessWaveControlBridgeExact.agda:canonicalWaveControlEvidence'
  'DASHI/Biology/MonsterWaveModeSeparatingProbeExact.agda:modeProbesSeparate'
  'DASHI/Biology/MonsterWaveModeSeparatingProbeExact.agda:sameMonsterLaneDoesNotDetermineGeometry'
  'DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda:criticalReflectionNegatesDisplacement'
  'DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda:reflectionDefectInvariant'
  'DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda:reflectionBlockDeterminantExact'
  'DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda:zetaBlockDeterminantReflectionInvariant'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

grep -q '10.1038/s41467-026-71386-z' DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda
grep -q '10.1016/j.neuron.2026.06.019' DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda
grep -q '10.1016/j.acha.2017.05.007' DASHI/Biology/QuaternionSymmetryResolvedWaveExact.agda
grep -q '10.31234/osf.io/z48x7_v3' DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda
grep -q '10.1093/cercor/bhag098' DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda
grep -q '10.1016/j.celrep.2025.115685' DASHI/Biology/ConsciousAccessWaveControlBridgeExact.agda
grep -q '10.48550/arXiv.2608.13637' DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda

grep -q 'finiteCharactersAreNotContinuumWaveNumbers' DASHI/Biology/BalancedTernaryFourierModeExact.agda
grep -q 'centerSignatureIsNotFullHelmholtzHodgeDecomposition' DASHI/Biology/FiniteTorusVectorWaveGeometryExact.agda
grep -q 'quaternionOrientationDoesNotReplaceFourierMode' DASHI/Biology/QuaternionSymmetryResolvedWaveExact.agda
grep -q 'finiteFeedbackDoesNotProveUniversalEphapticMechanism' DASHI/Biology/TravelingWaveFunctionalTopologyExact.agda
grep -q 'MonsterDimensionDoesNotIdentifyNeuralMode' DASHI/Biology/ConsciousAccessWaveControlBridgeExact.agda
grep -q 'orderThreePeriodDoesNotDeterminePhysicalGeometry' DASHI/Biology/MonsterWaveModeSeparatingProbeExact.agda
grep -q 'genericBlockIsNotIdentifiedWithAlpogeFurmanWeilBlock' DASHI/Mathematics/NumberTheory/RiemannReflectionOrbitDefectExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound10WaveSymmetryValidation.agda
