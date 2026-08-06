#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_frontier_hodge_automorphic_spectral_crosspollination.sh

files=(
  DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda
  DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda
  DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda
  DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
  DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraExact.agda
  DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraBridgeExact.agda
  DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda
  DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda
  DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
  DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda
  DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda
  DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda
  DASHI/Mathematics/CrossPollination/FrontierHodgeAutomorphicSpectralRound2Validation.agda
  DASHI/EverythingFrontierHodgeAutomorphicSpectralRound2.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "hardened frontier round two contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda:assembledCoordinatesReduce'
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda:hodgeCoordinateUniqueness'
  'DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda:canonicalHodgeDirectSumCertificate'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda:allProjectiveSpaceClassesAreDiagonal'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda:p2BettiVector'
  'DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda:p3DegreeTable'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:tableauRowCount'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:localConstraintCountEqualsSteps'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:boundedAcceptanceToAcceptingTableau'
  'DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda:acceptingTableauToBoundedAcceptance'
  'DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda:vacuumMinusOneIdentity'
  'DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda:translationMinusTwoVanishes'
  'DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda:truncatedVertexFieldsCommute'
  'DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraBridgeExact.agda:genericSquareZeroVertexCertificate'
  'DASHI/Moonshine/SquareZeroDifferentialVertexAlgebraBridgeExact.agda:genericAndConcreteFieldsAgree'
  'DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda:heisenbergRelationOnFiniteWindow'
  'DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda:numberEigenvalue3'
  'DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda:canonicalKernelReflectionPositive'
  'DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda:productMeasureFactorization'
  'DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda:connectedCorrelationVanishes'
  'DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda:finiteKPCriterion'
  'DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda:partitionFunctionIsFive'
  'DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda:volumeIndexedGapIsUniform'
  'DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda:finiteToyIsNotInteractingYangMills'
  'DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda:allRound2LocalStagesInhabited'
  'DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda:finiteOSModelsRemainInteractingBoundaries'
  'DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda:finiteGapRemainsContinuumBoundary'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "$file"
done

grep -Fq '10.2307/2373615' DASHI/Mathematics/LinearAlgebra/RationalThreeWayHodgeCoordinateUniquenessExact.agda
grep -Fq '10.1017/CBO9780511615344' DASHI/Mathematics/AlgebraicGeometry/ProjectiveSpaceHodgeBasisExact.agda
grep -Fq '10.1145/800157.805047' DASHI/Mathematics/Complexity/GenericFiniteRunTableauExact.agda
grep -Fq '10.1073/pnas.83.10.3068' DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
grep -Fq '10.1007/BF01645738' DASHI/Physics/Constructive/FiniteReflectionPositivityExact.agda
grep -Fq '10.1007/BF01608978' DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
grep -Fq '10.1007/BF01211762' DASHI/Physics/Constructive/FinitePolymerKPBudgetExact.agda

grep -Fq 'full formal Jacobi identity remain separate' DASHI/Moonshine/FiniteDifferentialVertexAlgebraExact.agda
grep -Fq 'full infinite Weyl algebra' DASHI/Moonshine/RankOneHeisenbergFockWindowExact.agda
grep -Fq 'not OS4 clustering for an interacting gauge measure' DASHI/Physics/Constructive/FiniteProductClusteringDenominatorClearedExact.agda
grep -Fq 'not the interacting nonabelian' DASHI/Physics/YangMills/YangMillsFiniteConstructiveLadderExact.agda
grep -Fq 'finiteOSModelsRemainInteractingBoundaries' DASHI/Mathematics/CrossPollination/FrontierProductiveCompletionRound2GateExact.agda

grep -Fq 'EverythingFrontierHodgeAutomorphicSpectralCrossPollination' DASHI/EverythingFrontierHodgeAutomorphicSpectralRound2.agda
grep -Fq 'FrontierHodgeAutomorphicSpectralRound2Validation' DASHI/EverythingFrontierHodgeAutomorphicSpectralRound2.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/EverythingFrontierHodgeAutomorphicSpectralRound2.agda
