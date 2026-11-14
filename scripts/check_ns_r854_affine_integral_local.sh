#!/usr/bin/env bash
# Local only, no CI status flags: original R854 scalar + Agda kernel receipt.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_ns_r854_original_affine_integrated_rate_exact.py
target=DASHI/Physics/Closure/NSTriadKNR650Rational345LipschitzIntegralRound854Exact.agda
python3 scripts/check_ns_r823_shear_negative_control_20261114.py
python3 scripts/check_ns_r853_quadratic_lie_derivative_20261114.py
target=DASHI/Physics/Closure/NSTriadKNR650Rational345RelaxedEnvelopeRound855Exact.agda
test -f "$target" || { echo "BLOCKED: missing $target" >&2; exit 11; }
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|--no-termination-check|allow-unsolved-metas' "$target"; then
  echo "BLOCKED: unfinished/unchecked R854 source" >&2
  exit 13
fi
command -v agda >/dev/null 2>&1 || {
  echo "BLOCKED: no Agda 2.9 kernel available, source-written != accepted" >&2
  exit 12
}
AGDA_JOBS=1 DASHI_NO_TMUX=1 \
  bash scripts/run_agda29_parallel_check.sh "$target"
echo "R854 original rational scalar Agda acceptance complete."
echo "R854/R855 original rational scalar Agda acceptance complete."
echo "Real R408 finite ODE trajectory and R853 integrated-source transport OPEN."
