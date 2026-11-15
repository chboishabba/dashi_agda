#!/usr/bin/env bash
# F1 actual gamma source: exhaustive all-bitword regression and exact
# physical-table positive/malformed-case Agda proof admission.
# This is NOT all N21 parsing, F2/F3/F4, or original InNP.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_karp21_literal_gamma_allwords_20261114.py
python3 scripts/check_karp21_gamma_all_length_physical.py

if [[ "${KARP_F1_SOURCE_ONLY:-0}" == "1" ]]; then
  echo "FINITE_EXHAUSTION_PASS: no pinned Agda acceptance; all original F3/F4 gates OPEN"
  exit 0
fi
if ! command -v agda >/dev/null 2>&1 && ! command -v nix >/dev/null 2>&1; then
  echo "BLOCKED: no Agda/Nix kernel runner, no source admission" >&2
  exit 12
fi
targets=(
  DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthFiniteTablePhysicalExact.agda
  DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthPrefixSimulationExact.agda
  DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthPayloadSimulationExact.agda
  DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthSeparatorAndHaltExact.agda
  DASHI/Mathematics/Complexity/Karp21NativeGammaAllLengthCompositePhysicalExact.agda
  DASHI/Mathematics/Complexity/Karp21NativeGammaPhysicalAcceptanceObservationExact.agda
)
for root in "${targets[@]}"; do
  test -f "$root" || { echo "BLOCKED: missing $root" >&2; exit 11; }
  if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|NO_TERMINATION_CHECK|TERMINATING|allow-unsolved-metas' "$root"; then
    echo "BLOCKED: unsafe or unsolved $root" >&2; exit 13
  fi
  AGDA_JOBS=1 DASHI_NO_TMUX=1 bash scripts/run_agda29_parallel_check.sh "$root"
done
echo "PINNED AGDA PASS: F1 literal gamma positive-word observation and malformed cases"
echo "OPEN: complete all-input physical source bisimulation, F2 heap, F3 N21, F4 bit clock, original InNP"
