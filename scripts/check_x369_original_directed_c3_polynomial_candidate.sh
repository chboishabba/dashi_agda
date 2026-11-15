#!/usr/bin/env bash
# Explicit NEW X369 F3 polynomial proof candidate checker.
#
# This target is NOT among the previously accepted 8 Track B leaves.
# Never merge its status into prior receipts without fresh Agda 2.9
# kernel validation. On failure, this runner exits nonzero.
set -euo pipefail
cd "$(dirname "$0")/.."
export DASHI_NO_TMUX=1
scripts/run_agda29_parallel_check.sh \
  DASHI/Cognition/PNF/X369OriginalDirectedTriadC3PolynomialCandidate.agda
echo "NEW original directed triad C3 polynomial candidate passed Agda kernel on this checkout."
