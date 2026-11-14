#!/usr/bin/env bash
# Original Clay multi-lane source convergence checker, 14 November 2026.
#
# Source-only mode (CLAY_SOURCE_ONLY=1) runs exact finite regressions and a
# local synthetic-Git planner suite, NEVER marks Agda/kernel accepted.
# Default mode additionally requires the repository's pinned Agda 2.9
# wrapper and an authoritative Nix/golden check chosen by the operator.
# Source donor/PR admission details: Docs/roadmaps/ClayPortfolioPinnedIntegration20261114.json.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python3 scripts/check_ns_r846_zero_mode_and_nonzero_support.py
python3 scripts/check_ns_r854_original_affine_integrated_rate_exact.py
python3 scripts/check_bsd_q2_39_coherent_hensel.py
python3 scripts/test_bsd_level32_positive_tail.py
python3 scripts/check_balaban_l1_adjoint_haar_local_tail.py
python3 scripts/check_bsd_k1_local_squareclass_parity.py
python3 scripts/check_ns_r854_original_affine_integrated_rate_exact.py
python3 scripts/check_clay_abc_attachment_negative_controls.py
python3 -m unittest discover -s tests -p 'test_clay_abc_attachment_negative_controls.py' -v
python3 -m unittest discover -s tests -p 'test_plan_clay_multi_pr_integrations.py' -v

ROOT_MODULE="DASHI/Mathematics/CrossPollination/ClayStagedSourceConvergence20261114.agda"

if [[ "${CLAY_SOURCE_ONLY:-0}" == "1" ]]; then
  echo "PASS: finite/source-only checks only. Agda golden, theorem acceptance and Clay promotion NOT CHECKED."
  exit 0
fi

if [[ ! -x scripts/run_agda29_parallel_check.sh ]]; then
  echo "BLOCKED: pinned Agda 2.9 checker unavailable; cannot promote source acceptance" >&2
  exit 2
fi

scripts/run_agda29_parallel_check.sh "$ROOT_MODULE"
echo "DRAFT only: Agda 2.9 worker check returned zero. The authoritative pinned Nix/golden"
echo "and transitive postulate/axiom/safety audit must be run before PR merging."
echo "No physical Clay endpoint is promoted by this source checker."
