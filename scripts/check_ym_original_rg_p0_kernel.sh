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
  # Prefer genuine original 1024-label -> F19 full interacting chain
  # before conditional cross-numerator or downstream E1/D1 compilers.
  DASHI/Physics/YangMills/YMClayNativeClosedThreeEqualitiesCandidateExact.agda
  DASHI/Physics/YangMills/YMClayNative1024ClosedReindexHaarConsequencesExact.agda
  DASHI/Physics/YangMills/YMClayNative1024WeightedWilsonReindexExact.agda
  DASHI/Physics/YangMills/YMClayNativePairsSpectatorsFubiniExact.agda
  DASHI/Physics/YangMills/YMClaySUNWeightedDisjointPairFibreReparamExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonF19ConcreteWeightExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonPhysicalF19PartitionExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonPairSpectatorDecoderExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonCanonicalMarkedReindexExact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.agda
  DASHI/Physics/YangMills/YMClayOriginalWilsonPartitionEqualityDoesNotBoundRGExact.agda
  DASHI/Physics/YangMills/YMClayP0FGeneratedTwoSourceInteractionNegativeControlExact.agda
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
  DASHI/Physics/YangMills/YMClaySUNFinitePairedHaarBlockPushforwardExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalAxialBondParityInjectiveExact.agda
  DASHI/Physics/YangMills/YMClayR445NativePairHolonomyIdentityExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalNativeParityPairWeldExact.agda
  DASHI/Physics/YangMills/YMClayR445CanonicalBondPermutationCodecExact.agda
  DASHI/Physics/YangMills/YMClayR445FlatPairedHaarIntegrationExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalPureHaarBlockWeldExact.agda
  DASHI/Physics/YangMills/YMClayR445OriginalFullWilsonFiberDensityExact.agda
  DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda
)

for target in "${targets[@]}"; do
  if [[ ! -f "$target" ]]; then
    printf 'MISSING original proof source: %s\n' "$target" >&2
    exit 2
  fi
done

# Prefer the already pinned local Agda 2.9 executable, if supplied.
# The common runner otherwise invokes Nix even on a PATH-only host, so
# AGDA_BIN must be populated explicitly for a true PATH-first fallback.
if [[ -n "${AGDA_BIN:-}" ]] && command -v "$AGDA_BIN" >/dev/null 2>&1; then
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
  runner=(bash scripts/run_agda29_parallel_check.sh)
elif command -v nix >/dev/null 2>&1; then
  runner=(nix develop .# --command bash scripts/run_agda29_parallel_check.sh)
else
  echo 'BLOCKED: neither AGDA_BIN nor PATH Agda nor Nix is available; no kernel receipt' >&2
  exit 127
fi
printf 'Checking %s exact original Wilson proof targets at head %s\n' \
  "${#targets[@]}" "$(git rev-parse HEAD 2>/dev/null || printf unknown)"
# No CI; selected exact original source and dependencies are checked locally.
DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
  "${runner[@]}" "${targets[@]}"

echo 'PASS: original Wilson P0 focused Agda kernel root accepted.'
