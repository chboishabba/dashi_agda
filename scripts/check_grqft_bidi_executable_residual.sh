#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"

files=(
  DASHI/Physics/Foundations/SameCandidateQFTGRRecoveryExact.agda
  DASHI/Physics/Foundations/GRQFTStressWeldBidiAttemptExact.agda
  DASHI/Physics/Closure/DiscreteWarpedEinsteinMatterModel.agda
  DASHI/Physics/Closure/EinsteinEquationBidiResidualExact.agda
  DASHI/Physics/Closure/EinsteinEquationBidiResidualValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe' "${files[@]}"; then
  echo "GRQFT executable residual tranche contains a hole, postulate, unsafe escape, or trust primitive" >&2
  exit 1
fi

tmp_json="$(mktemp)"
trap 'rm -f "$tmp_json"' EXIT
python3 scripts/grqft_einstein_bidi_harness.py --output "$tmp_json" >/dev/null
diff -u outputs/grqft_einstein_bidi_residual.json "$tmp_json"

cache_root="${DASHI_AGDA29_CACHE_ROOT:-${RUNNER_TEMP:-$root/.cache}/dashi-agda29-grqft-bidi}"
export DASHI_AGDA29_CACHE_ROOT="$cache_root"
export DASHI_STATUS_DIR="${DASHI_STATUS_DIR:-$cache_root/status}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$cache_root/xdg}"
mkdir -p "$DASHI_STATUS_DIR" "$XDG_CACHE_HOME"
export AGDA_LOG_PATH="${AGDA_LOG_PATH:-$root/grqft-bidi-executable-residual-agda.log}"
export AGDA_JOBS="${AGDA_JOBS:-4}"
export DASHI_NO_TMUX="1"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/GRQFTStressWeldBidiAttemptExact.agda \
  DASHI/Physics/Closure/EinsteinEquationBidiResidualValidation.agda
