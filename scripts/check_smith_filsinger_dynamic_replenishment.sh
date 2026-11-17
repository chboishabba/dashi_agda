#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
MODE="${1:-tests}"
if [[ "$MODE" != "tests" && "$MODE" != "--agda" ]]; then
  echo "Usage: $0 [tests|--agda]" >&2
  exit 2
fi
target="DASHI/Physics/Motors/SmithFilsingerReplenishedCycleCapExact.agda"
phase_owner="DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda"
python_tests=(
  scripts/test_smith_filsinger_midpoint_phase_work.py
  scripts/test_smith_filsinger_midpoint_dc_source_matching.py
  scripts/test_smith_filsinger_dynamic_replenishment.py
  scripts/test_smith_filsinger_phase_maxcut_exact.py
  scripts/test_smith_filsinger_f10_f13_field_bridge.py
  scripts/test_smith_filsinger_nonlinear_retarded_source_port.py
  scripts/test_smith_filsinger_distributed_causal_energy.py
  scripts/test_smith_filsinger_spatial_chain_exact.py
  scripts/test_smith_filsinger_finite_volume_face_incidence_exact.py
  scripts/test_smith_filsinger_indexed_face_incidence_exact.py
  scripts/test_smith_filsinger_indexed_signed_cell_stokes_exact.py
  scripts/test_smith_filsinger_full_vector_indexed_face_sample_exact.py
  scripts/test_smith_filsinger_space_time_poynting_telescope_exact.py
  scripts/test_smith_filsinger_coercive_green_retarded_weld_exact.py
  scripts/test_smith_filsinger_layered_green_sympy.py
  scripts/test_smith_filsinger_tangential_maxwell_sympy.py
  scripts/test_smith_filsinger_radiation_green_sympy.py
  scripts/test_smith_filsinger_oblique_maxwell_sympy.py
  scripts/test_smith_filsinger_passive_radiation_sympy.py
  scripts/test_smith_filsinger_periodic_fourier_green_sympy.py
  scripts/test_smith_filsinger_lorentz_ade_sympy.py
  scripts/test_smith_filsinger_lorentz_maxwell_weld_sympy.py
  scripts/test_smith_filsinger_local_causal_ade_sympy.py
  scripts/test_smith_filsinger_cayley_coefficients_sympy.py
  scripts/test_smith_filsinger_cayley_midpoint_sympy.py
  scripts/test_smith_filsinger_indexed_cayley_face_sympy.py
  scripts/test_smith_filsinger_plane_wave_spacetime_exact.py
)
test -s "$target"
test -s "$phase_owner"
for f in "${python_tests[@]}";do test -s "$f";done
if grep -nE '^[[:space:]]*postulate([[:space:]]|$)|\\{!!\\}' "$target" "$phase_owner";then
  echo "Unjustified postulate or Agda hole" >&2
  exit 1
fi
PYTHONDONTWRITEBYTECODE=1 python -m pytest -q "${python_tests[@]}"
if [[ "$MODE" == "--agda" ]];then
  scripts/run_agda29_parallel_check.sh "$target" "$phase_owner"
  echo "PASS pinned Agda replenished-cycle + finite phase source owners"
else
  echo "Python tests passed; Agda kernel NOT checked. Use --agda on pinned host."
fi
