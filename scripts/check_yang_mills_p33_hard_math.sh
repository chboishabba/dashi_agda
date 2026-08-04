#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

export AGDA_JOBS="${AGDA_JOBS:-1}"

files=(
  DASHI/Physics/YangMills/BalabanPath4GeneratedLDLCertificate.agda
  DASHI/Physics/YangMills/BalabanP33FiniteSignedRemainderSummationExact.agda
  DASHI/Physics/YangMills/BalabanP33Path4SignedRemainderCoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33FiveChannelPath4CoercivityExact.agda
  DASHI/Physics/YangMills/BalabanP33HardMathValidation.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}' "${files[@]}"; then
  echo "P33 hard-math tranche contains an explicit postulate or hole" >&2
  exit 1
fi

grep -q 'path4LDLDecompositionRaw = ℚRing.solve-∀' \
  DASHI/Physics/YangMills/BalabanPath4GeneratedLDLCertificate.agda
grep -q 'globalRemainderLowerBound' \
  DASHI/Physics/YangMills/BalabanP33FiniteSignedRemainderSummationExact.agda
grep -q 'p33SmallFieldRadius = + 1 / 8192' \
  DASHI/Physics/YangMills/BalabanP33Path4SignedRemainderCoercivityExact.agda
grep -q 'path4ConfiguredRadiusPhysicalCoercive' \
  DASHI/Physics/YangMills/BalabanP33Path4SignedRemainderCoercivityExact.agda
grep -q 'fiveLocalChannelsGivePath4PhysicalCoercivity' \
  DASHI/Physics/YangMills/BalabanP33FiveChannelPath4CoercivityExact.agda

grep -q '10.1007/BF01240355' \
  DASHI/Physics/YangMills/BalabanP33Path4SignedRemainderCoercivityExact.agda
grep -q '10.1007/BF01211042' \
  DASHI/Physics/YangMills/BalabanP33FiveChannelPath4CoercivityExact.agda
grep -q '10.1017/CBO9781139020411' \
  DASHI/Physics/YangMills/BalabanPath4GeneratedLDLCertificate.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/YangMills/BalabanP33HardMathValidation.agda
