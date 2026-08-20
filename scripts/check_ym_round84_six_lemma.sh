#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

target="DASHI/Physics/YangMills/BalabanClayHighestAlphaRound84Validation.agda"
test -f "$target"

# The generic runner historically defaults its pre-tmux status directory to a
# developer-local /home/c path before it later establishes XDG_CACHE_HOME.  CI
# runners cannot create that directory.  Pin both caches to a caller-supplied or
# repository-local writable path BEFORE invoking the generic checker.
cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-round84}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"

files=(
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound84Validation.agda
  DASHI/Physics/YangMills/BalabanBetaHistoryLocalizedInfluenceExact.agda
  DASHI/Physics/YangMills/BalabanSharedMarkedAnalyticShellExact.agda
  DASHI/Physics/YangMills/BalabanCompactSimplePositiveBetaFromSharedMarkedShellExact.agda
  DASHI/Physics/YangMills/CompactSimpleClassificationAdjointCasimirExact.agda
  DASHI/Physics/YangMills/BalabanCMP109CompactSimpleColourReductionSourceExact.agda
  DASHI/Physics/YangMills/BalabanCompactSimpleHaarQuadraticCasimirExact.agda
  DASHI/Physics/YangMills/BalabanReducedGhostPrincipalLogDetSourceExact.agda
  DASHI/Physics/YangMills/BalabanFiniteTraceSeriesPrefixTailExact.agda
  DASHI/Physics/YangMills/BalabanPolchinskiShellIntegralDebtExact.agda
  DASHI/Physics/YangMills/YangMillsSharedMarkedCompositeOPERemainderExact.agda
  DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda
  DASHI/Physics/YangMills/YangMillsStressWardStoneGeneratorBridgeExact.agda
)

for file in "${files[@]}"; do
  test -f "$file"
done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "Round84 six-lemma tranche contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

# Ensure the authoritative root really states the current count and the critical
# trust-boundary corrections, rather than merely importing older scoreboards.
grep -q 'round84HardAnalyticLemmaUpperCount = 6' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda
grep -q 'marginal running coupling' \
  DASHI/Physics/YangMills/BalabanBetaHistoryLocalizedInfluenceExact.agda
grep -q 'betaMark hessianMark compositeMark' \
  DASHI/Physics/YangMills/BalabanSharedMarkedAnalyticShellExact.agda
grep -q 'sameFamilyStressWardGeneratesOSTranslationsLevel' \
  DASHI/Physics/YangMills/BalabanClayHighestAlphaRound84SixAnalyticLemmaExact.agda

a="${AGDA_LOG_PATH:-$root/ym-round84-agda.log}"
export AGDA_LOG_PATH="$a"
export AGDA_JOBS="${AGDA_JOBS:-4}"

scripts/run_agda29_parallel_check.sh "$target"
