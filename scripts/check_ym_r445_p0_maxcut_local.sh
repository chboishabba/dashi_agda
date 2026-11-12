#!/usr/bin/env bash
set -euo pipefail

# Authoritative local Agda 2.9 check for the newly source-written
# R445 P0.A-E native finite-bond/weighted-density maximum cut.
# Nix required, no Docker, no CI admission, fail on the first error.
# The physical P0.F/E1/D1/D2/N1/G1 gates are NOT checked/closed here.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Physics/YangMills/YMClayR445OriginalAxialBondParityInjectiveExact.agda
  DASHI/Physics/YangMills/YMClayR445NativePairHolonomyIdentityExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalNativeParityPairWeldExact.agda
  DASHI/Physics/YangMills/YMClayR445CanonicalBondPermutationCodecExact.agda
  DASHI/Physics/YangMills/YMClaySUNOneLinkHaarConvolutionSourceExact.agda
  DASHI/Physics/YangMills/YMClaySUNTwoLinkHaarEffectiveFiberDensityExact.agda
  DASHI/Physics/YangMills/YMClaySUNFinitePairedHaarBlockPushforwardExact.agda
  DASHI/Physics/YangMills/YMClayR445FlatPairedHaarIntegrationExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalPureHaarBlockWeldExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalFullWilsonFiberDensityExact.agda
  DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda
)
for target in "${targets[@]}"; do
  if [[ ! -f "$target" ]]; then
    echo "FAIL missing original source: $target" >&2
    exit 2
  fi
done
if ! command -v nix >/dev/null 2>&1; then
  echo "Nix unavailable: no local Agda kernel receipt" >&2
  exit 127
fi
printf 'Original R445 P0.A-E checked source head: %s\n' \
  "$(git rev-parse HEAD 2>/dev/null || echo unknown)"
for target in "${targets[@]}"; do
  echo "CHECK $target"
  DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
    nix develop .# --command bash scripts/run_agda29_parallel_check.sh "$target"
done
echo "PASS: all local R445 P0.A-E source targets accepted by Agda."
echo "NOTE: conditional permutation/native vector weld fields require actual inhabitants."
echo "NOTE: no physical UV RG, continuum or Clay spectral gate is closed."
