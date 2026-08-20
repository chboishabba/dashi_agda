#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

# VALIDATION-ONLY TEMPORARY ROUTER.
#
# This branch exists only to obtain an observable PR-associated run from a
# workflow already present on the default branch.  The substantive Round-7
# branch does not modify this NS checker.  Route the hosted Nix/Agda runner to
# the complete Round-7 checker, which itself cascades through its Round-6 base.
bash scripts/check_ssp15_j_stratified_quotient_multiresolution_round7.sh
