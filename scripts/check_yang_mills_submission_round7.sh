#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/YangMills/YangMillsSubmissionPrimarySourceLedger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionObligationCardinalityExact.agda
  DASHI/Physics/YangMills/BalabanP06OwnedGraphCombinatoricsExact.agda
  DASHI/Physics/YangMills/BalabanP11UniformAbsorptionReductionExact.agda
  DASHI/Physics/YangMills/LocalLatticeP11SubmissionBridgeExact.agda
  DASHI/Physics/YangMills/BalabanBishopHalfBallSquareReductionExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionTypedLimitEndpointExact.agda
  DASHI/Physics/YangMills/YangMillsSubmissionExactCutset.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound7Ledger.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound7Receipt.agda
  DASHI/Physics/YangMills/YangMillsSubmissionRound7Validation.agda
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerSubmissionRound7Advance.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "round-seven submission tranche contains a postulate or explicit hole" >&2
  exit 1
fi

# The exact inventory deliberately distinguishes the 191 theorem spine from
# the 219-item full A-I submission inventory.
grep -q 'theoremSpineObligationCount ≡ 191' \
  DASHI/Physics/YangMills/YangMillsSubmissionObligationCardinalityExact.agda
grep -q 'fullSubmissionObligationCount ≡ 219' \
  DASHI/Physics/YangMills/YangMillsSubmissionObligationCardinalityExact.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP06OwnedGraphCombinatoricsExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP11UniformAbsorptionReductionExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/LocalLatticeP11SubmissionBridgeExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanBishopHalfBallSquareReductionExact.agda
scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/YangMillsSubmissionRound7Validation.agda
