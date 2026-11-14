#!/usr/bin/env bash
set -euo pipefail

# Native Nix/Agda 2.9 verification. No Docker or CI requirement.
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Physics/YangMills/YMClayP0BishopRealCarrierInstancesExact.agda
  DASHI/Physics/YangMills/YMClayP0BishopToOriginalWilsonRealWeldExact.agda
  DASHI/Physics/YangMills/YMClayP0OriginalPartitionBishopApartnessExact.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || {
    echo "missing or empty Agda source: $source" >&2
    exit 1
  }
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|TERMINATING|NON_COVERING' "$source"; then
    echo "forbidden source-level trust escape in $source" >&2
    exit 1
  fi
  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "unsolved hole in $source" >&2
    exit 1
  fi
done

# A whole-graph --safe run on the legacy Wilson target would be INVALID:
# YMClayP0BishopToOriginalWilsonRealWeldExact imports
# DASHI.Foundations.RealAnalysisAxioms, which openly POSTULATES its Real
# carrier and ordered-ring laws. Source-local "no postulate" grep does not
# remove or whitelist transitive postulates. Keep two explicit receipts:
#
#   (a) constructed Bishop-only source, checked with --safe;
#   (b) original selected Wilson scalar socket, ordinarily typechecked
#       but with its known RealAnalysisAxioms postulates disclosed.
#
# Neither creates OriginalWilsonToBishopScalarWeld or removes an axiom.
#
# --safe on (b) is deliberately NOT attempted or represented as achieved.
bishop_source="${sources[0]}"
legacy_sources=("${sources[1]}" "${sources[2]}")
# The shared script's default AGDA_BIN invokes Nix even with Agda on
# PATH. Preserve the explicit user's pinned choice and accept PATH-only
# checked executables; otherwise let the native Nix fallback run.
if [[ -z "${AGDA_BIN:-}" ]] && command -v agda >/dev/null 2>&1; then
  export AGDA_BIN="$(command -v agda)"
fi

echo "CHECK safe constructed Bishop-only target: $bishop_source"
DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
  bash scripts/run_agda29_parallel_check.sh --safe "$bishop_source"

for legacy_source in "${legacy_sources[@]}"; do
  if ! grep -q 'DASHI.Foundations.RealAnalysisAxioms' "$legacy_source"; then
    # The second target is expected to import the postulated carrier
    # directly, and the third indirectly. A build-time attribution scan
    # must not silently equate source no-postulate with transitive safety.
    if [[ "$legacy_source" == *"BishopToOriginalWilson"* ]]; then
      echo "FAIL expected legacy RealAnalysisAxioms dependency" >&2
      exit 2
    fi
  fi
done
echo "CHECK legacy original Wilson targets: imports RealAnalysisAxioms postulates"
DASHI_NO_TMUX=1 AGDA_JOBS="${AGDA_JOBS:-1}" \
  bash scripts/run_agda29_parallel_check.sh "${legacy_sources[@]}"

echo "PASS: Bishop-only safe check and legacy source typechecking completed."
echo "TRUST: original Wilson real postulates remain an explicit dependency."
echo "OPEN: faithful Bishop↔original Wilson real scalar interpretation; physical RG."
