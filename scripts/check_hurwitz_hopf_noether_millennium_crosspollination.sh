#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_yang_mills_clay_highest_alpha_round30.sh

files=(
  DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda
  DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda
  DASHI/Mathematics/Algebra/CompositionAlgebraCoreExact.agda
  DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda
  DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
  DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda
  DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda
  DASHI/Mathematics/Symmetry/KleinGroupActionInvariantExact.agda
  DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda
  DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
  DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda
  DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda
  DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda
  DASHI/Physics/YangMills/YangMillsKleinNoetherGaugeInvariantBridgeExact.agda
  DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
  DASHI/Physics/Closure/NavierStokesKleinCriticalScalingExact.agda
  DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda
  DASHI/Mathematics/CrossPollination/HurwitzHopfNoetherMillenniumCrossPollinationValidation.agda
  DASHI/EverythingHurwitzHopfNoetherCrossPollination.agda
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
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda:octonionNormMultiplicative'
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda:octonionLeftAlternative'
  'DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda:e124AssociativityFails'
  'DASHI/Mathematics/Algebra/CompositionAlgebraCoreExact.agda:quaternionAssociativeCompositionCore'
  'DASHI/Mathematics/Algebra/CompositionAlgebraCoreExact.agda:octonionAlternativeCompositionCore'
  'DASHI/Mathematics/Algebra/CompositionAlgebraCoreExact.agda:octonionAssociativityFailure'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda:FrobeniusClassificationTheorem'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda:HurwitzClassificationTheorem'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda:ConcreteToClassificationBridge'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda:frobeniusCandidateImpliesHurwitzCandidate'
  'DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda:octonionSeparatesTheTwoCandidateTables'
  'DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda:noetherianityIsNotVariationalSymmetry'
  'DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda:deltaMultiplicative'
  'DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda:deltaCoassociative'
  'DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda:leftAntipodeIdentity'
  'DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda:hopfAlgebraIsNotHopfFibration'
  'DASHI/Mathematics/Symmetry/KleinGroupActionInvariantExact.agda:invariantOnOrbit'
  'DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda:coupledNonlinearCancellation'
  'DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda:hurwitzDimensionToHopfDimension'
  'DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda:quaternionHopfRadiusIdentity'
  'DASHI/Mathematics/Topology/QuaternionHopfRadiusExact.agda:unitPairMapsToTargetUnitQuadric'
  'DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda:hopfQuaternionRightScales'
  'DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda:hopfQuaternionRightUnitInvariant'
  'DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda:unitQuaternionRightAction'
  'DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda:hopfScalarKleinInvariant'
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
grep -q 'No DOI assigned or verified for the original book' DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda
grep -q '10.1007/BF01448439' DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda
grep -q '10.1080/03081087.2020.1761281' DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda
grep -q '10.1007/BF01448439' DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
grep -q '10.1080/03081087.2020.1761281' DASHI/Mathematics/Algebra/HurwitzFrobeniusLawProfileExact.agda
grep -q '10.1007/BF01464225' DASHI/Mathematics/Algebra/NoetherianityMeaningSeparationExact.agda
grep -q '10.1007/978-1-4612-0783-2' DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda
grep -q '10.1007/BFb0101433' DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda
grep -q '10.48550/arXiv.physics/0503066' DASHI/Mathematics/Symmetry/NoetherDissipationDefectExact.agda
grep -q '10.2307/1970147' DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
grep -q '10.1007/BF01457962' DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda
grep -q '10.1016/0370-2693(75)90163-X' DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
grep -q '10.1007/BF00253344' DASHI/Physics/Closure/NavierStokesKleinCriticalScalingExact.agda
grep -q '10.1017/S0022112069000991' DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda

grep -q 'does not claim the real analytic division property' DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda
grep -q 'does not prove the analytic real division property' DASHI/Mathematics/Algebra/CayleyDicksonRationalOctonionExact.agda
grep -q 'do not manufacture the real analytic' DASHI/Mathematics/Algebra/CompositionAlgebraCoreExact.agda
grep -q 'No inhabitant of the theorem records is supplied' DASHI/Mathematics/Algebra/HurwitzFrobeniusClassificationBoundary.agda
grep -q 'does not identify this finite cocommutative example' DASHI/Mathematics/Algebra/RationalC2HopfAlgebraExact.agda
grep -q 'does not prove Adams' DASHI/Mathematics/Topology/HopfInvariantOneDimensionGateExact.agda
grep -q 'does not prove that every geometric fibre is exactly one such orbit' DASHI/Mathematics/Topology/QuaternionHopfUnitOrbitExact.agda
grep -q 'No topological identity is promoted' DASHI/Physics/YangMills/YangMillsHurwitzHopfStructuralGateExact.agda
grep -q 'does not identify every vortex field with a Hopf field' DASHI/Physics/Closure/NavierStokesHopfNoetherContinuationGateExact.agda
grep -q 'proves no Millennium problem' DASHI/Mathematics/CrossPollination/MillenniumProblemStructuralRelevanceGateExact.agda

grep -q 'import DASHI.Everything' DASHI/EverythingHurwitzHopfNoetherCrossPollination.agda
grep -q 'HurwitzHopfNoetherMillenniumCrossPollinationValidation' DASHI/EverythingHurwitzHopfNoetherCrossPollination.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingHurwitzHopfNoetherCrossPollination.agda
