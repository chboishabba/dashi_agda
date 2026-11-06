#!/usr/bin/env bash
# P00/P11 #1460: invoke repository Agda29 PARALLEL CHECKER, not direct Nix
# or an unpinned system Agda. This wrapper owns compiler, stdlib,
# vendor/bishop, cache, parallelism, RSS limits, logs, status and tmux.
# SOURCE typechecks != transitive axiomatic trust != PHYSICAL proof.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

echo "DASHI_UNIFICATION_HEAD=$(git rev-parse HEAD 2>/dev/null || echo UNAVAILABLE)"
python3 scripts/check_emergent31_complete_186_status_20261104.py
python3 scripts/check_tsfv_unification_48_phase_cut_20261106.py
python3 scripts/check_tsvf_original_os_strong_domain_bidi_20261105.py
python3 scripts/check_tsfv_original_diamond_spatial_bits_bidi_20261105.py
python3 scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py

# Reuse the canonical 2.9 checker environment; wrapper owns the toolchain
# or an independent 'agda -l standard-library' command here.
parallel_checker="$root/scripts/run_agda29_parallel_check.sh"
test -f "$parallel_checker"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-tsfv}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$cache_root/tsfv-parallel-check.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME" "$(dirname "$AGDA_LOG_PATH")"

safe_sources=(
  DASHI/Physics/Foundations/TSFVKKSelectedHorizontalMetricSchurExact.agda
  DASHI/Physics/Foundations/TSFVSelectedLatticeAcousticKKFlatControlExact.agda
  DASHI/Physics/Foundations/TSFVAcousticMassInverseBidiNoGoExact.agda
  DASHI/Physics/Foundations/TSFVAcousticLocalImpulseThirdDerivativeExact.agda
  DASHI/Physics/Foundations/TSFVKKHorizontalReductionNoninjectiveBidiExact.agda
  DASHI/Physics/Foundations/TSVFOSSelectedKetHamiltonianNonpromotionExact.agda
  DASHI/Physics/Foundations/TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact.agda
)
roots=(
  DASHI/Unified/BalabanRGTOERegression.agda
  DASHI/Unified/TSFVUnifiedRegression.agda
  DASHI/Unified/TSFVParentChildRegression.agda
)
for file in "${safe_sources[@]}" "${roots[@]}"; do
  test -f "$file"
done

# Local fail-closed structural trust checks of the selected own modules;
# the transitive dependency graph and mathematical axioms require a
# separately reviewed proof authority report, even after typechecking.
if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|--type-in-type|primTrustMe|trustMe' "${safe_sources[@]}"; then
  echo "P00/S11 unsafe local selected source / hole / unreviewed axiom" >&2
  exit 1
fi

echo "P00/S11: parallel_checker --safe, ${#safe_sources[@]} selected candidates"
"$parallel_checker" --safe "${safe_sources[@]}"

echo "P00/S11: parallel_checker, ${#roots[@]} parent/child transitive roots"
"$parallel_checker" "${roots[@]}"

echo "SOURCE_KERNEL_CHECK_COMPLETED; review transitive axioms and original PHYSICAL E1 separately"
