#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round5.sh

files=(
  DASHI/Biology/MonsterFilteredCarrierExact.agda
  DASHI/Biology/MonsterRepresentationRoutesExact.agda
  DASHI/Biology/MonsterCompatibilityComplexExact.agda
  DASHI/Biology/MonsterTrivialReductionBoundaryExact.agda
  DASHI/Biology/MonsterWholeCarrierActionSchemaExact.agda
  DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
  DASHI/Biology/ConsciousAccessRound6MonsterFilteredCarrierValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "round six contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

checks=(
  'MonsterFilteredCarrierExact.agda:totalCandidateDimensionExact'
  'MonsterFilteredCarrierExact.agda:dashIAssociatedGraded'
  'MonsterFilteredCarrierExact.agda:sixByNineReductionOrigin'
  'MonsterRepresentationRoutesExact.agda:filtrationAssessment'
  'MonsterRepresentationRoutesExact.agda:mixingAssessment'
  'MonsterRepresentationRoutesExact.agda:bulkNotPreservedBySwap'
  'MonsterCompatibilityComplexExact.agda:sourceDimensionExact'
  'MonsterCompatibilityComplexExact.agda:cohomologyRoute'
  'MonsterTrivialReductionBoundaryExact.agda:sixByNineTrivialReduction'
  'MonsterTrivialReductionBoundaryExact.agda:canonicalMonsterReductionBoundary'
  'MonsterWholeCarrierActionSchemaExact.agda:mixTwiceIsIdentity'
  'MonsterWholeCarrierActionSchemaExact.agda:fullyMixedCandidate'
  'MonsterSubgroupBranchingBenchmarksExact.agda:babyMonsterRestrictionDimensionExact'
  'MonsterSubgroupBranchingBenchmarksExact.agda:conwayTwoLocalDimensionExact'
  'MonsterSubgroupBranchingBenchmarksExact.agda:CandidateSubgroupTest'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Biology/$file"
done

grep -q '10.1007/BF01389186' DASHI/Biology/MonsterFilteredCarrierExact.agda
grep -q '10.1007/BF01232032' DASHI/Biology/MonsterFilteredCarrierExact.agda
grep -q '10.1007/978-1-4612-0979-9' DASHI/Biology/MonsterTrivialReductionBoundaryExact.agda
grep -q '10.1007/BF01388521' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
grep -q '10.1515/jgth.1998.023' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
grep -q '10.1017/CBO9780511730054.019' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda
grep -q 'gradedPiecesAreMonsterInvariantIsFalse' DASHI/Biology/MonsterFilteredCarrierExact.agda
grep -q 'anyConcreteMonsterRouteCompletedIsFalse' DASHI/Biology/MonsterRepresentationRoutesExact.agda
grep -q 'actualDifferentialConstructedIsFalse' DASHI/Biology/MonsterCompatibilityComplexExact.agda
grep -q 'fiftyThreeIsClaimedMonsterIrrepIsFalse' DASHI/Biology/MonsterTrivialReductionBoundaryExact.agda
grep -q 'schemaConstructsMonsterActionIsFalse' DASHI/Biology/MonsterWholeCarrierActionSchemaExact.agda
grep -q 'dashiTenTernaryPlusReducedNotYetPublishedBranching' DASHI/Biology/MonsterSubgroupBranchingBenchmarksExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound6MonsterFilteredCarrierValidation.agda
