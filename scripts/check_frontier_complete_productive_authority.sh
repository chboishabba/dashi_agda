#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_frontier_hodge_automorphic_spectral_crosspollination.sh

files=(
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessFinalExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda
  DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda
  DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda
  DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
  DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraExact.agda
  DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraBridgeExact.agda
  DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda
  DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda
  DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
  DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda
  DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityGateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityValidation.agda
  DASHI/EverythingFrontierCompleteProductiveAuthority.agda
)

for file in "${files[@]}"; do test -f "$file"; done

superseded=(
  DASHI/Physics/Constructive/FiniteProductClusteringExact.agda
  DASHI/Physics/YangMills/YangMillsFiniteOS2OS4KPBridgeExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgePatternExact.agda
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeUniquenessExact.agda
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda
  DASHI/Moonshine/RankOneHeisenbergFiniteWindowExact.agda
  DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierHodgeAutomorphicSpectralRound2Validation.agda
  DASHI/EverythingFrontierHodgeAutomorphicSpectralRound2.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveCompletionGateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveValidation.agda
  DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveValidationStatus.agda
  DASHI/EverythingFrontierCompleteProductiveValidation.agda
  scripts/check_frontier_hodge_automorphic_spectral_round2.sh
  scripts/check_frontier_complete_productive_validation.sh
  .github/workflows/frontier-hodge-automorphic-spectral-round2.yml
  .github/workflows/frontier-complete-productive-validation.yml
  .github/workflows/frontier-superseded-cleanup.yml
  .github/workflows/frontier-final-cleanup.yml
  .github/workflows/frontier-final-cleanup-v2.yml
)

for file in "${superseded[@]}"; do
  if [[ -e "$file" ]]; then
    echo "superseded or intermediate frontier file remains present: $file" >&2
    exit 1
  fi
done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "direct complete authority contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessFinalExact.agda:coordinateUniqueness'
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessFinalExact.agda:coordinatesOfAnyDecomposition'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda:allProjectiveSpaceClassesAreDiagonal'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda:p2BettiVector'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:localConstraintCountEqualsSteps'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:acceptingTableauToBoundedAcceptance'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerHomomorphism'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerInjective'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerSurjective'
  'DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda:finiteKummerKernelTrivial'
  'DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda:truncatedVertexFieldsCommute'
  'DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraBridgeExact.agda:genericSquareZeroVertexCertificate'
  'DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda:heisenbergRelationOnFiniteWindow'
  'DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda:numberEigenvalue3'
  'DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda:canonicalKernelReflectionPositive'
  'DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda:connectedCorrelationVanishes'
  'DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda:finiteKPCriterion'
  'DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda:partitionFunctionIsFive'
  'DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda:volumeIndexedGapIsUniform'
  'DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda:finiteToyIsNotInteractingYangMills'
  'DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityGateExact.agda:allDirectAuthorityObjectivesInhabited'
  'DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityGateExact.agda:finiteProofCannotEqualContinuumBoundary'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

grep -Fq '10.2307/2373615' DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessFinalExact.agda
grep -Fq '10.1017/CBO9780511615344' DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda
grep -Fq '10.1145/800157.805047' DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda
grep -Fq '10.1007/978-0-387-09494-6' DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda
grep -Fq '10.1073/pnas.83.10.3068' DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
grep -Fq '10.1007/BF01645738' DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda
grep -Fq '10.1007/BF01608978' DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
grep -Fq '10.1007/BF01211762' DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda

grep -Fq 'full formal Jacobi identity remain separate' DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
grep -Fq 'finite oscillator algebra beneath the Fock grading' DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda
grep -Fq 'not OS4 clustering for an interacting gauge measure' DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
grep -Fq 'neither the interacting nonabelian' DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda
grep -Fq 'RemainingAuthorityBoundary' DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityGateExact.agda

grep -Fq 'FrontierHodgeAutomorphicSpectralValidation' DASHI/Mathematics/CrossPollination/FrontierCompleteProductiveAuthorityValidation.agda
grep -Fq 'EverythingFrontierHodgeAutomorphicSpectralCrossPollination' DASHI/EverythingFrontierCompleteProductiveAuthority.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingFrontierCompleteProductiveAuthority.agda
