#!/usr/bin/env bash
set -euo pipefail

targets=(
  DASHI/Moonshine/Monster196883BabyBranchPrimeSupportExact.agda
  DASHI/Moonshine/MonsterBinaryTernaryInformationDepthExact.agda
  DASHI/Moonshine/JMDGF4096MonsterTwoLocalProvenanceExact.agda
  DASHI/Moonshine/JMDMonsterRepresentationCrossPollinationMaxCutExact.agda
)

for target in "${targets[@]}"; do
  test -f "$target"
done

# Prime-support / branching owner.
grep -q 'babyMonsterBranchingExact' "${targets[0]}"
grep -q 'babyMonster4371Factorization' "${targets[0]}"
grep -q 'monster196883OggFactorization' "${targets[0]}"
grep -q 'branchPrimeSupportDoesNotExplainBranching' "${targets[0]}"
grep -q 'babyMonsterBranchDoesNotSelectTwoBTateQ10' "${targets[0]}"

# Binary/ternary information depth.
grep -q 'monsterOrderExact' "${targets[1]}"
grep -q 'twoPow179BelowMonster' "${targets[1]}"
grep -q 'monsterBelowTwoPow180' "${targets[1]}"
grep -q 'threePow112BelowMonster' "${targets[1]}"
grep -q 'monsterBelowThreePow113' "${targets[1]}"
grep -q 'monsterBitDepthIs180' "${targets[1]}"
grep -q 'monsterTritDepthIs113' "${targets[1]}"
grep -q 'jmdSpreadExact' "${targets[1]}"

# 4096 dual-role provenance.
grep -q 'gf4096CardinalityRole' "${targets[2]}"
grep -q 'monsterTwoLocal4096Role' "${targets[2]}"
grep -q 'sameScalar4096' "${targets[2]}"
grep -q 'sameScalarDoesNotIdentify4096Roles' "${targets[2]}"
grep -q 'gf4096DoesNotConstructMonsterTwoLocalModule' "${targets[2]}"

# Cross-pollination capstone: same ambient 196883, distinct sourced decompositions.
grep -q 'sameAmbientTwoBranchings' "${targets[3]}"
grep -q 'babyAndTwoLocalBranchingsRechart196883' "${targets[3]}"
grep -q 'jmdCrossPollinationDoesNotConstructTwoBTateQ10' "${targets[3]}"
grep -q 'primeSupportAnd4096DoNotBecomeSameRepresentationMeaning' "${targets[3]}"

scripts/run_agda29_parallel_check.sh "${targets[@]}"
