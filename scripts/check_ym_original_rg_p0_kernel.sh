#!/usr/bin/env bash
set -euo pipefail

# Local, fail-closed, Nix-provided Agda 2.9 acceptance of the actual
# original Wilson R445 E1/D1 proof cut. No CI, no Docker, no implicit
# promotion from a source-written declaration to a kernel theorem.
#
# Run from repository root on the PR #1444 branch:
#   bash scripts/check_ym_original_rg_p0_kernel.sh
#
# Preserves the project's pinned wrapper, standard library, cache
# and resource guard; prints original checker diagnostics on failure.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

targets=(
  DASHI/Physics/YangMills/YMClayOriginalRealSubtractionInterchangeExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalR445ThreeMomentRGCutExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteNumeratorOrderExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalR445BoundedMomentMajorantsExact.agda
  DASHI/Physics/YangMills/YMClayE1A3OriginalR445WeightedCrossNumeratorExact.agda
  DASHI/Physics/YangMills/YMClayE1D1CrossNumeratorCenteringExact.agda
  DASHI/Physics/YangMills/YMClayE1D1CrossNumeratorCenteringAlgebraExact.agda
  DASHI/Physics/YangMills/YMClayOriginalPlaquetteTraceCyclicityInsufficientExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalSUNTraceToAllWordsBoundExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalSignedWilsonWordMomentBoundExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalWilsonWordConcatenationR445Exact.agda
  DASHI/Physics/YangMills/YMClayRealSubtractionLawIndependenceExact.agda
  DASHI/Physics/YangMills/YMClayE1D1CrossNumeratorCenteringDoesNotForceContractionExact.agda
  DASHI/Physics/YangMills/YMClayE1D1OriginalCrossNumeratorNormalizedMomentFactorExact.agda
  DASHI/Physics/YangMills/YMClayD2ObservedDecayDoesNotForceFullSpectralGapExact.agda
  DASHI/Physics/YangMills/BalabanSU2RationalWilsonTraceBoundExact.agda
  DASHI/Physics/YangMills/YMClayP0BishopRealCarrierInstancesExact.agda
  DASHI/Physics/YangMills/YMClayP0BishopToOriginalWilsonRealWeldExact.agda
  DASHI/Physics/YangMills/YMClaySUNOneLinkHaarConvolutionSourceExact.agda
  DASHI/Physics/YangMills/YMClaySUNTwoLinkHaarEffectiveFiberDensityExact.agda
  DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda
)

for target in "${targets[@]}"; do
  if [[ ! -f "$target" ]]; then
    printf 'MISSING original proof source: %s\n' "$target" >&2
    exit 2
  fi
done

if ! command -v nix >/dev/null 2>&1; then
  echo 'Nix unavailable: local Agda acceptance NOT performed' >&2
  exit 127
fi

printf 'Checking %s exact original Wilson proof targets at head %s\n' \
  "${#targets[@]}" "$(git rev-parse HEAD 2>/dev/null || printf unknown)"

# The project-owned runner (not independent CI) owns Agda version,
# stdlib, memory ceilings, diagnostics and its kernel pass/fail result.
DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
  nix develop .# --command \
  bash scripts/run_agda29_parallel_check.sh "${targets[@]}"

echo 'PASS: original Wilson P0 focused Agda kernel root accepted.'
