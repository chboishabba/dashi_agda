#!/usr/bin/env bash
# Focused, fail-closed original-source NS R846/R847/R848 2-branch checker.
# Authoritative acceptance requires pinned local Agda 2.9, not GitHub CI.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_ns_r846_zero_mode_and_nonzero_support.py

for target in \
  DASHI/Physics/Closure/NSTriadKNR650Rational345ZeroOutputSupportCounterexampleRound847Exact.agda \
  DASHI/Physics/Closure/NSTriadKNR650Rational345ForcingSupportMaxCutRound846Exact.agda \
  DASHI/Physics/Closure/NSTriadKNR650Rational345NonzeroSupportRound848Exact.agda
do
  echo "KERNEL TARGET: $target"
  AGDA_JOBS=1 DASHI_NO_TMUX=1 \
    bash scripts/run_agda29_parallel_check.sh "$target"
done
echo "PINNED AGDA 2.9 SOURCE TRANSPORT ACCEPTED; real R830 ODE and Clay NS remain OPEN."
