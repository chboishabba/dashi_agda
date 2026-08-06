#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_hurwitz_hopf_noether_millennium_crosspollination.sh

files=(
  DASHI/Analysis/RiemannMaassMoonshineCrossPollinationExact.agda
  DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda
  DASHI/Moonshine/MonsterGradedVOABridgeExact.agda
  DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda
  DASHI/Mathematics/NumberTheory/RiemannCompletedZetaBoundary.agda
  DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineHodgeDiamondExact.agda
  DASHI/Mathematics/AlgebraicGeometry/HodgeNoetherianVOACrossPollination.agda
  DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda
  DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda
  DASHI/Mathematics/Arithmetic/EllipticCurveHodgeFrobeniusCrossPollination.agda
  DASHI/Mathematics/Complexity/PolynomialReductionExact.agda
  DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda
  DASHI/Mathematics/Topology/RoundThreeSphereRicciFlowExact.agda
  DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda
  DASHI/Mathematics/Topology/QuaternionS3PoincareCrossPollination.agda
  DASHI/Mathematics/CrossPollination/MillenniumSubstantiveCrossPollinationGateExact.agda
  DASHI/Mathematics/CrossPollination/MillenniumSubstantiveCrossPollinationValidation.agda
  DASHI/EverythingMillenniumSubstantiveCrossPollination.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "substantive Millennium tranche contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda:conjugationCommutesWithFunctionalReflection'
  'DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda:criticalLineFixedByReflection'
  'DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda:reflectionFixedImpliesCriticalLine'
  'DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda:zeroQuartet'
  'DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda:hilbertPolyaCandidateZerosLieOnCriticalLine'
  'DASHI/Mathematics/NumberTheory/RiemannCompletedZetaBoundary.agda:completedZetaZeroSymmetry'
  'DASHI/Mathematics/NumberTheory/RiemannCompletedZetaBoundary.agda:RiemannHypothesis'
  'DASHI/Analysis/RiemannMaassMoonshineCrossPollinationExact.agda:representedSpectralZerosAreCritical'
  'DASHI/Analysis/RiemannMaassMoonshineCrossPollinationExact.agda:maassSpectrumIsNotRiemannZeroSpectrum'
  'DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda:identityTraceCoefficientIsDimension'
  'DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda:gradedRepresentationIsNotVOA'
  'DASHI/Moonshine/MonsterGradedVOABridgeExact.agda:monsterIdentityCoefficientIsGradeDimension'
  'DASHI/Moonshine/MonsterGradedVOABridgeExact.agda:firstMoonshineArithmeticReused'
  'DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda:cycleClassProducesRationalHodgeClass'
  'DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda:cycleClassOfSumIsHodgeSum'
  'DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda:cycleClassOfScalarMultipleIsHodgeScalarMultiple'
  'DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda:hodgeConjectureGivesCycleRepresentative'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineHodgeDiamondExact.agda:p1HodgeConjugationSymmetry'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveLineHodgeDiamondExact.agda:p1BettiNumbers'
  'DASHI/Mathematics/AlgebraicGeometry/HodgeNoetherianVOACrossPollination.agda:noetherianityDoesNotProveHodgeDecomposition'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda:curveDiscriminantIsSixtyFour'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda:p5ProjectivePointCountIsEight'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda:frobeniusTraceAtFiveIsMinusTwo'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda:localFactorAtFiveCoefficients'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda:p5HasseBoundChecked'
  'DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda:BSDRankConjecture'
  'DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda:bsdFormulaSymmetricForm'
  'DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda:localFactorDoesNotGiveBSD'
  'DASHI/Mathematics/Arithmetic/EllipticCurveHodgeFrobeniusCrossPollination.agda:ellipticHodgeConjugationSymmetry'
  'DASHI/Mathematics/Arithmetic/EllipticCurveHodgeFrobeniusCrossPollination.agda:ellipticBettiNumbers'
  'DASHI/Mathematics/Complexity/PolynomialReductionExact.agda:composeReduction'
  'DASHI/Mathematics/Complexity/PolynomialReductionExact.agda:pullbackPAlongReduction'
  'DASHI/Mathematics/Complexity/PolynomialReductionExact.agda:npCompleteInPImpliesPEqualsNP'
  'DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda:excludedMiddleFormulaIsTautology'
  'DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda:gctObstructionSeparatesWitnessedOrbits'
  'DASHI/Mathematics/Topology/RoundThreeSphereRicciFlowExact.agda:roundFlowSemigroup'
  'DASHI/Mathematics/Topology/RoundThreeSphereRicciFlowExact.agda:roundExtinctionAtConfiguredTime'
  'DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda:geometrizationAndSphericalClassificationGivePoincare'
  'DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda:existingGeometrizationAuthorityIsFalse'
  'DASHI/Mathematics/Topology/QuaternionS3PoincareCrossPollination.agda:poincareConclusionFromQuaternionBridge'
  'DASHI/Mathematics/CrossPollination/MillenniumSubstantiveCrossPollinationGateExact.agda:allOpenLanesRemainUncompleted'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

# Source metadata guards.
grep -q '10.1007/BF01232032' DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda
grep -q '10.1186/s40687-015-0029-6' DASHI/Moonshine/MonsterGradedVOABridgeExact.agda
grep -q '10.1017/CBO9780511615344' DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda
grep -q '10.1007/978-0-387-09494-6' DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda
grep -q '10.1515/crll.1965.218.79' DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda
grep -q '10.1145/800157.805047' DASHI/Mathematics/Complexity/PolynomialReductionExact.agda
grep -q '10.1137/S009753970038715X' DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda
grep -q '10.4310/jdg/1214436922' DASHI/Mathematics/Topology/RoundThreeSphereRicciFlowExact.agda
grep -q '10.48550/arXiv.math/0211159' DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda

# Scope and non-promotion guards.
grep -q 'does not construct V\^natural' DASHI/Moonshine/GradedVertexOperatorAlgebraBoundary.agda
grep -q 'does not construct analytic continuation' DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda
grep -q 'None of the analytic fields is filled' DASHI/Mathematics/NumberTheory/RiemannCompletedZetaBoundary.agda
grep -q 'No Hodge-conjecture solution' DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda
grep -q 'not a construction of the global L-function' DASHI/Mathematics/Arithmetic/EllipticCurveFrobeniusExact.agda
grep -q 'No canonical inhabitant' DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda
grep -q 'Cook--Levin.*remain separate obligations' DASHI/Mathematics/Complexity/PolynomialReductionExact.agda
grep -q 'No Cook--Levin tableau construction' DASHI/Mathematics/Complexity/CookLevinCircuitGCTBoundary.agda
grep -q 'not short-time existence for arbitrary metrics' DASHI/Mathematics/Topology/RoundThreeSphereRicciFlowExact.agda
grep -q 'does not supply smooth Ricci flow with surgery' DASHI/Mathematics/Topology/PoincareGeometrizationExactBoundary.agda
grep -q 'allOpenLanesRemainUncompleted' DASHI/Mathematics/CrossPollination/MillenniumSubstantiveCrossPollinationGateExact.agda

grep -q 'import DASHI.EverythingHurwitzHopfNoetherCrossPollination' DASHI/EverythingMillenniumSubstantiveCrossPollination.agda
grep -q 'MillenniumSubstantiveCrossPollinationValidation' DASHI/EverythingMillenniumSubstantiveCrossPollination.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingMillenniumSubstantiveCrossPollination.agda
