#!/usr/bin/env bash
# Local-only, checkpointed 90-second per-fixture max-cut. No GitHub Actions.
set -euo pipefail
cd "$(dirname "$0")"
PYTHON="${PYTHON:-python3}"
TIMEOUT_SECONDS="${TIMEOUT_SECONDS:-90}"
RECEIPTS="${RECEIPTS:-./solar_maxcut_receipts}"
mkdir -p "$RECEIPTS"
for entry in \
  check_solar_native_contract_sympy.py \
  check_solar_indexed_stage_tangent_sympy.py \
  check_passive_global_exact_sympy.py \
  check_squared_restoration_sympy.py \
  check_frozen_population_identity.py \
  check_solar_material_cache_parity.py \
  check_solar_rational_reflection_box.py \
  check_solar_spherical_reverse_integration.py; do
  if [[ ! -f "$entry" ]]; then
    echo "MISSING_SOURCE: $entry" >&2
    exit 2
  fi
  hash="$(sha256sum "$entry" | cut -d ' ' -f1)"
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
