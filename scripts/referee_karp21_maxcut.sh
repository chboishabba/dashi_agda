#!/usr/bin/env bash
# Deterministic, fail-closed Karp-21 Agda proof referee.
# This script does not install Agda, modify CI or assume source claims
# are kernel-checked. It exits nonzero on the first missing prerequisite
# or Agda diagnostic and prints the pinned local revision.
#
# Usage:
#   bash scripts/referee_karp21_maxcut.sh golden
#   bash scripts/referee_karp21_maxcut.sh e20
#   bash scripts/referee_karp21_maxcut.sh all
#   bash scripts/referee_karp21_maxcut.sh preflight
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
mode="${1:-all}"

if ! command -v python3 >/dev/null 2>&1; then
  echo "BLOCKED: python3 unavailable for preflight." >&2
  exit 127
fi

case "$mode" in
  golden|e20|all|preflight) ;;
  *)
    echo "Usage: $0 {preflight|golden|e20|all}" >&2
    exit 2
    ;;
esac

if [[ "$mode" != "preflight" ]] && ! command -v agda >/dev/null 2>&1; then
  echo "BLOCKED: agda executable unavailable. No kernel proof receipt." >&2
  exit 127
fi

printf 'Repository: %s\n' "$repo_root"
printf 'Referee revision: '
git rev-parse HEAD
if command -v agda >/dev/null 2>&1; then
  printf 'Agda version: '
  agda --version
else
  # The Python/static preflight must run even without Agda installed.
  # All kernel modes have already failed closed above.
  printf 'Agda version: unavailable (preflight-only; no kernel receipt)\n'
fi
printf 'Mode: %s\n' "$mode"

# This source/bitword preflight is independent of the Agda kernel.
# It catches actual codec mismatches and stdlib argument-arity mistakes.
python3 scripts/check_karp21_reserved_formula_constructors.py
# Guard against unsound old-locality -> new-unique-head promotion.
python3 scripts/check_karp21_tape_boundary_ghost.py
python3 scripts/check_karp21_tape_guarded_uniqueness_small.py
python3 scripts/check_karp21_canonical_endcap_cnf.py
python3 scripts/check_karp21_guarded_sat_same_object.py
python3 scripts/check_karp21_uniform_row_width.py
python3 scripts/check_karp21_agda_stdlib_arity.py
python3 scripts/check_karp21_e20_bitlength_bound.py --max-n 5
python3 scripts/check_karp_binary_codec.py
python3 scripts/check_karp21_binary_native_sparse_verifier.py
python3 scripts/check_karp21_conway_gamma_reference.py
python3 scripts/check_karp21_binary_word_equality.py
python3 scripts/check_karp21_gamma_binary_native.py
python3 scripts/check_karp21_gamma_binary_native_signed.py
python3 scripts/check_karp21_native_bitword_sparse_verifier.py
python3 scripts/check_karp21_finfree_word_comparison_bound.py
python3 scripts/check_karp21_finfree_raw_primitive_comparisons.py
# Native gamma, binary addition, signed ledger and threshold regressions.
python3 scripts/check_karp21_signed_gamma_allwords.py
python3 scripts/check_karp21_binary_native_ripple.py
python3 scripts/check_karp21_native_signed_ledger.py
python3 scripts/check_karp21_ssp_residual.py
python3 scripts/check_karp21_positive_gamma.py
python3 scripts/check_karp21_native_prefix_trie_consistency.py
python3 scripts/check_karp21_native_signed_trace_factor.py
python3 scripts/check_karp21_binary_native_threshold.py
python3 scripts/check_karp21_fractran_priority_frontier.py
python3 scripts/check_karp21_fractran_n21_edge.py
python3 scripts/check_karp21_fractran_original_raw_trace.py

if [[ "$mode" == "preflight" ]]; then
  echo "PREFLIGHT ONLY: no Agda kernel acceptance or machine clock."
  exit 0
fi

export DASHI_AGDA_RSS_LIMIT_MB="${DASHI_AGDA_RSS_LIMIT_MB:-16384}"

if [[ -z "${AGDA_BIN:-}" ]]; then
  if [[ -x "/nix/store/jv7cagyh8wm4cw8j94z5s2ffqmjv10dq-Agda-2.9.0-bin/bin/agda" ]]; then
    export AGDA_BIN="/nix/store/jv7cagyh8wm4cw8j94z5s2ffqmjv10dq-Agda-2.9.0-bin/bin/agda"
  fi
fi

check_agda() {
  local source="$1"
  printf '\nREFEREE CHECK: %s\n' "$source"
  if [[ -f "scripts/run_agda29_parallel_check.sh" ]] && { [[ -n "${AGDA_BIN:-}" && -x "$AGDA_BIN" ]] || command -v nix >/dev/null 2>&1; }; then
    DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh "$source"
  else
    local shadow_dir
    shadow_dir="$(mktemp -d /tmp/dashi-referee-agda.XXXXXX)"
    rsync -a --prune-empty-dirs \
      --include='*/' \
      --include='*.agda' \
      --include='*.lagda*' \
      --exclude='*' \
      "$repo_root/" "$shadow_dir/"
    local -a include_args=(-i "$shadow_dir" --no-libraries --no-default-libraries)
    if [[ -n "${AGDA_STDLIB_ROOT:-}" ]]; then
      include_args+=(-i "$AGDA_STDLIB_ROOT")
    fi
    agda "${include_args[@]}" "$shadow_dir/$source"
    rm -rf "$shadow_dir"
  fi
  printf 'ACCEPTED BY AGDA: %s\n' "$source"
}

if [[ "$mode" == "golden" || "$mode" == "all" ]]; then
  for root in \
    DASHI.Mathematics.Complexity.Karp21CompilerRepairGovernanceExact \
    DASHI.Mathematics.Complexity.Karp21CookGoldenEverything \
    DASHI.Mathematics.Complexity.Karp21GammaGoldenEverything \
    DASHI.Mathematics.Complexity.Karp21FinDecoderIndexBidiExact \
    DASHI.Mathematics.Complexity.Karp21BinaryFinMaterializationCostExact
  do
    python3 scripts/check_karp21_golden_agda_import_closure.py \
      --entry "$root"
  done

  check_agda DASHI/Mathematics/Complexity/Karp21ConwayTotalChainExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21ConwayGammaChainCodecExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21N21BitWeightedComparisonEnvelopeExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryWordEqualityPrimitiveExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryEqualitySameValueExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativePayloadExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativeSignedExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativeAllWordNumericalWeldExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativeAllWordValidityExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativeSignedAllWordValidityExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativeSignedInspectionClockExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeRippleAdderExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeRippleAdderValueExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FractranPriorityFrontierExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeSignedLedgerExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeThresholdExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaBinaryNativePositiveThresholdExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeEndpointPrefixTrieExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeMultiplicityScaleExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeSignedTraceFactorExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeSignedTraceFactorSemanticExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryNativeSignedTraceFactorC2Exact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21CompilerRepairGovernanceExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21CookGoldenEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaGoldenEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinDecoderIndexBidiExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryFinMaterializationCostExact.agda
fi

if [[ "$mode" == "e20" || "$mode" == "all" ]]; then
  # These graph integration roots are intentionally not declared
  # --safe. Kernel typechecking is still required and must fail-closed.
  check_agda DASHI/Mathematics/Complexity/ConcreteTapeBoundaryGuardFocusedRootExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21RawGraphValidatorObservationExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21CanonicalRawValidatorCompleteExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21OriginalGammaGraphWordFieldsReplayExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21PositiveThresholdGammaExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeRawSparseWordVerifierExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeRawValidatorComparisonCountExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeAllWordValidationClockExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeOriginalWordComparisonBoundExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeOriginalGraphComparisonEnvelopeExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21N21SameWordCountedAcceptanceExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FractranN21EndpointScoreStepExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FractranOriginalRawTraceReplayExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FractranOriginalTypedTraceAcceptanceExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryRuntimeEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21SignedSSPOrientationNoLosslessExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21Everything.agda
fi

printf '\nCHECKED: selected Agda roots at pinned local HEAD.\n'
printf 'WARNING: This is NOT a receipt for Karp-21 NP-completeness,\n'
printf 'machine polynomial clocks, or any unimplemented E01–E19 reductions.\n'
