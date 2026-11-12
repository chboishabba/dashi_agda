#!/usr/bin/env bash
set -euo pipefail

# Authoritative local Agda 2.9 check for the newly source-written
# R445 P0.A-E native finite-bond/weighted-density maximum cut.
# AGDA_BIN, PATH Agda or Nix supported; no Docker or CI, fail on first error.
# The physical P0.F/E1/D1/D2/N1/G1 gates are NOT checked/closed here.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  # Original owners first: fail at the genuine canonical label Bool/refl
  # and same-Wilson weighted F18/F19 source, not at downstream adapters.
  DASHI/Physics/YangMills/YMClayNativeClosedThreeEqualitiesCandidateExact.agda
  DASHI/Physics/YangMills/YMClayNative1024ClosedReindexHaarConsequencesExact.agda
  DASHI/Physics/YangMills/YMClayNative1024WeightedWilsonReindexExact.agda
  DASHI/Physics/YangMills/YMClaySUNWeightedDisjointPairFibreReparamExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonF19ConcreteWeightExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonPhysicalF19PartitionExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalAxialBondParityInjectiveExact.agda
  DASHI/Physics/YangMills/YMClayR445NativePairHolonomyIdentityExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalNativeParityPairWeldExact.agda
  DASHI/Physics/YangMills/YMClayR445CanonicalBondPermutationCodecExact.agda
  DASHI/Physics/YangMills/YMClaySUNOneLinkHaarConvolutionSourceExact.agda
  DASHI/Physics/YangMills/YMClaySUNTwoLinkHaarEffectiveFiberDensityExact.agda
  DASHI/Physics/YangMills/YMClaySUNFinitePairedHaarBlockPushforwardExact.agda
  DASHI/Physics/YangMills/YMClayR445FlatPairedHaarIntegrationExact.agda
  DASHI/Physics/YangMills/YMClayR445AdjacentHaarPermutationCompilerExact.agda
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
# Supplementary exact finite regressions, not kernel acceptance.
python3 scripts/check_ym_r445_canonical_bond_codec_exact.py
python3 scripts/check_ym_r445_adjacent_schedule_exact.py
python3 scripts/check_ym_r445_kernel_valued_haar_exact.py

# The project runner resolves and version-checks AGDA_BIN/PATH/Nix.
# Avoid blocking a locally pinned Agda 2.9 executable just because
# Nix is not installed; no CI is required or consulted.
if [[ -n "${AGDA_BIN:-}" ]] && command -v "$AGDA_BIN" >/dev/null 2>&1; then
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v agda >/dev/null 2>&1; then
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v nix >/dev/null 2>&1; then
  runner=(nix develop .# --command bash scripts/run_agda29_parallel_check.sh)
else
  echo "BLOCKED: no AGDA_BIN, PATH Agda or Nix. No kernel receipt." >&2
  exit 127
fi
printf 'Original R445 P0.A-E local source head: %s\n' \
  "$(git rev-parse HEAD 2>/dev/null || echo unknown)"
for target in "${targets[@]}"; do
  echo "CHECK $target"
  DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" "${runner[@]}" "$target"
done
echo "PASS: all local R445 P0.A-E source targets accepted by Agda."
echo "NOTE: conditional permutation/native vector weld fields require actual inhabitants."
echo "NOTE: no physical UV RG, continuum or Clay spectral gate is closed."
