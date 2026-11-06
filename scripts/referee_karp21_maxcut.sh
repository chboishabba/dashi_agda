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
python3 scripts/check_karp21_agda_stdlib_arity.py
python3 scripts/check_karp21_e20_bitlength_bound.py --max-n 5
python3 scripts/check_karp_binary_codec.py
python3 scripts/check_karp21_binary_native_sparse_verifier.py

if [[ "$mode" == "preflight" ]]; then
  echo "PREFLIGHT ONLY: no Agda kernel acceptance or machine clock."
  exit 0
fi

check_agda() {
  local source="$1"
  printf '\nREFEREE CHECK: %s\n' "$source"
  local -a include_args=(-i .)
  # Explicit stdlib source root for clean CI/ephemeral environments.
  # Locally registered Agda libraries continue working unchanged.
  if [[ -n "${AGDA_STDLIB_ROOT:-}" ]]; then
    include_args+=(-i "$AGDA_STDLIB_ROOT")
  fi
  agda "${include_args[@]}" "$source"
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

  check_agda DASHI/Mathematics/Complexity/Karp21CompilerRepairGovernanceExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21CookGoldenEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21GammaGoldenEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinDecoderIndexBidiExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryFinMaterializationCostExact.agda
fi

if [[ "$mode" == "e20" || "$mode" == "all" ]]; then
  # These graph integration roots are intentionally not declared
  # --safe. Kernel typechecking is still required and must fail-closed.
  check_agda DASHI/Mathematics/Complexity/Karp21RawGraphValidatorObservationExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21CanonicalRawValidatorCompleteExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21OriginalGammaGraphWordFieldsReplayExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21PositiveThresholdGammaExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21FinFreeRawSparseWordVerifierExact.agda
  check_agda DASHI/Mathematics/Complexity/Karp21BinaryRuntimeEverything.agda
  check_agda DASHI/Mathematics/Complexity/Karp21Everything.agda
fi

printf '\nCHECKED: selected Agda roots at pinned local HEAD.\n'
printf 'WARNING: This is NOT a receipt for Karp-21 NP-completeness,\n'
printf 'machine polynomial clocks, or any unimplemented E01–E19 reductions.\n'
