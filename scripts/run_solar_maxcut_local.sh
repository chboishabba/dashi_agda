#!/usr/bin/env bash
# Local-only, checkpointed 90-second per-fixture max-cut. No GitHub Actions.
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-90}"
RECEIPTS="${RECEIPTS:-./solar_maxcut_receipts}"
mkdir -p "$RECEIPTS"
# Invalidate cached checkpoints when sibling Python dependencies change.
# Conservative scope: all Python files in this script directory and this runner.
source_hash="$(find . -maxdepth 1 -type f \( -name '*.py' -o -name 'run_solar_maxcut_local.sh' \) -print0 | sort -z | xargs -0 sha256sum | sha256sum | cut -d ' ' -f1)"
for entry in \
  check_solar_native_contract_sympy.py \
  check_solar_indexed_stage_tangent_sympy.py \
  check_passive_global_exact_sympy.py \
  check_two_load_bernstein_sympy.py \
  check_four_world_source_off_sympy.py \
  check_solar_four_world_interaction_sympy.py \
  check_solar_zero_population_stratified_sympy.py \
  check_solar_support_transition_sympy.py \
  check_solar_support_boundary_cayley_sympy.py \
  check_solar_common_atlas_sympy.py \
  check_solar_common_atlas_native.py \
  check_solar_support_transition_native.py \
  check_solar_amplitude_path_sympy.py \
  check_solar_amplitude_event.py \
  check_solar_quadratic_jet.py \
  check_solar_passive_restoration_box.py \
  check_squared_restoration_sympy.py \
  check_frozen_population_identity.py \
  check_solar_material_cache_parity.py \
  check_solar_rational_reflection_box.py \
  check_solar_spherical_material_atlas.py \
  check_solar_spherical_reverse_integration.py \
  check_solar_spherical_reverse_atlas.py \
  check_solar_spherical_quadratic_path.py \
  check_solar_spherical_two_jet.py; do
  if [[ ! -f "$entry" ]]; then
    echo "MISSING_SOURCE: $entry" >&2
    exit 2
  fi
  hash="$(printf '%s\n' "$source_hash" "$(sha256sum "$entry")" | sha256sum | cut -d ' ' -f1)"
  status="$RECEIPTS/$entry.$hash.status"
  log="$RECEIPTS/$entry.$hash.log"
  if [[ -f "$status" ]] && [[ $(cat "$status") == PASS ]]; then
    echo "CACHED PASS $entry $hash"
    continue
  fi
  echo "RUN $entry $hash"
  if timeout "${TIMEOUT_SECONDS}s" "$PYTHON" "$entry" >"$log" 2>&1; then
    echo PASS >"$status"
    echo "PASS $entry"
  else
    code=$?
    printf 'EXIT_%s\n' "$code" >"$status"
    echo "FAIL $entry exit=$code; see $log" >&2
    exit "$code"
  fi
done
