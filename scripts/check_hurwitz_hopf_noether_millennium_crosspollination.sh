#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round30.sh

files=(
  DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda
  DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
  DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda
  DASHI/Mathematics/Symmetry/KleinGroupActionInvariantExact.agda
  DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda
  DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
  DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda
  DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda
  DASHI/Physics/YangMills/YangMillsKleinNoetherGaugeInvariantBridgeExact.agda
  DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
  DASHI/Physics/Closure/NavierStokesKleinCriticalScalingExact.agda
  DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda
  DASHI/Mathematics/CrossPollination/HurwitzHopfNoetherMillenniumCrossPollinationValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "cross-pollination tranche contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda:cayleyDicksonMultiplyMatchesQuaternion'
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda:quaternionNormMultiplicative'
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda:cayleyDicksonNormMultiplicative'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda:frobeniusCandidateImpliesHurwitzCandidate'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda:octonionSeparatesTheTwoCandidateTables'
  'DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda:noetherianityIsNotVariationalSymmetry'
  'DASHI/Mathematics/Symmetry/KleinGroupActionInvariantExact.agda:invariantOnOrbit'
  'DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda:coupledNonlinearCancellation'
  'DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda:hurwitzDimensionToHopfDimension'
  'DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda:quaternionHopfRadiusIdentity'
  'DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda:unitPairMapsToTargetUnitQuadric'
  'DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda:frobeniusMeaningsAreDistinct'
  'DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda:bsdUsesArithmeticNotRealDivisionFrobenius'
  'DASHI/Physics/YangMills/YangMillsKleinNoetherGaugeInvariantBridgeExact.agda:gaugeEquivalentConfigurationsHaveEqualAction'
  'DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda:sharedQuaternionCarrier'
  'DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda:fixedLatticeClusteringStillNotContinuumGap'
  'DASHI/Physics/Closure/NavierStokesKleinCriticalScalingExact.agda:serrinLInfinityTimeL3SpaceExact'
  'DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda:criticalScalingIsNotContinuation'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

grep -q '10.1090/S0273-0979-01-00934-X' DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda
grep -q '10.1007/BF01448439' DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
grep -q '10.1080/03081087.2020.1761281' DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
grep -q '10.1007/BF01464225' DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda
grep -q '10.48550/arXiv.physics/0503066' DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda
grep -q '10.2307/1970147' DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
grep -q '10.1016/0370-2693(75)90163-X' DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
grep -q '10.1007/BF00253344' DASHI/Physics/Closure/NavierStokesKleinCriticalScalingExact.agda
grep -q '10.1017/S0022112069000991' DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda

grep -q 'does not claim the real analytic division property' DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda
grep -q 'does not prove Adams' DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
grep -q 'No topological identity is promoted' DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
grep -q 'does not identify every vortex field with a Hopf field' DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda
grep -q 'proves no Millennium problem' DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Mathematics/CrossPollination/HurwitzHopfNoetherMillenniumCrossPollinationValidation.agda
