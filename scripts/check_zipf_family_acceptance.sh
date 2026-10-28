#!/usr/bin/env bash
# Zipf-family 27-topic acceptance -- never report kernel success from pytest.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPATH="$root/scripts${PYTHONPATH:+:$PYTHONPATH}"
if git rev-parse HEAD >/dev/null 2>&1; then
  echo "SOURCE_COMMIT=$(git rev-parse HEAD)"
else
  echo 'SOURCE_COMMIT=not_a_git_checkout'
fi
python3 -m pytest -q \
  tests/test_zipf_family_formal.py \
  tests/test_zipf_f13_pnf_parity_exact.py \
  tests/test_zipf_f13b_raw_rational_proof_exact.py \
  tests/test_zipf_f13b_h15_boundary_exact.py \
  tests/test_zipf_h14_novelty_curve_exact.py \
  tests/test_zipf_first_discovery_plackett_luce_exact.py \
  tests/test_zipf_abc_six_order_receipt.py \
  tests/test_zipf_ternary27_action_heaps_exact.py \
  tests/test_zipf_full_heaps_path_distribution_exact.py \
  tests/test_zipf_s24_monotone_path_transport_exact.py \
  tests/test_zipf_s24_majorization_chain_exact.py \
  tests/test_zipf_s24_pair_switch_constructive_exact.py \
  tests/test_zipf_family_crosslaw.py \
  tests/test_zipf_heaps_bridge_exact.py \
  tests/test_zipf_heaps_extremal_profiles.py \
  tests/test_zipf_majorization_expected_heaps_exact.py \
  tests/test_zipf_stochastic_majorization_exact.py \
  tests/test_zipf_completion_time_exact.py \
  tests/test_zipf_discovery_fit_stability_exact.py \
  tests/test_zipf_occupancy_collisions_exact.py \
  tests/test_pareto_benford_lorenz_bridge.py \
  tests/test_zipf_family_coverage_gates.py \
  tests/test_zipf_family_severe_coverage.py \
  tests/test_zipf_rank_model_evidence_exact.py \
  tests/test_zipf_clauset_words30_source_receipt.py
printf '%s\n' 'FINITE_PYTHON_TESTS_PASSED'
if ! command -v agda >/dev/null 2>&1; then
  printf '%s\n' 'AGDA_KERNEL_PENDING: Agda binary unavailable (overall acceptance withheld)' >&2
  exit 2
fi
agda -i . -l standard-library DASHI/Statistics/ZipfFamilyEverything.agda
printf '%s\n' 'ZIPF_FAMILY_AGDA_KERNEL_CHECK_PASSED'
