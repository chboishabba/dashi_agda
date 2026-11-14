#!/usr/bin/env bash
# Fail-closed RH A2/G3 attachment audit; do not confuse finite diagnostic
# with original selected-witness A2, selected zeros or RH G3 kernel acceptance.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
python3 scripts/check_rh_a2_g3_attachment_maxcut_20261114.py
python3 scripts/check_rh_g3_quartic_signed_cone_geometry.py

if [[ -z "${RH_LEAN_REPO_DIR:-}" ]]; then
  echo "BLOCKED: set RH_LEAN_REPO_DIR to the checked-out dashi_lean4 #108 branch" >&2
  echo "Finite exact diagnostics PASS != original RH proof/kernel receipt" >&2
  exit 12
fi
target="${RH_LEAN_REPO_DIR}/Synthesis/RiemannA2G3PoleAndSignedHeatNegativeControls.lean"
if [[ ! -f "$target" ]]; then
  echo "BLOCKED: missing Lean negative-control module: $target" >&2
  exit 13
fi
command -v lake >/dev/null 2>&1 || {
  echo "BLOCKED: no Lake / Lean pinned toolchain" >&2
  exit 14
}
(cd "$RH_LEAN_REPO_DIR" && lake env lean Synthesis/RiemannA2G3PoleAndSignedHeatNegativeControls.lean)
echo "LEAN PASS: *auxiliary* RH A2 pole and two-mode signed-heat negative controls"
echo "OPEN: original selected witness K, FarHorizontal CH, zero cofinal compensation, Route B cap/outer limits, RH"
