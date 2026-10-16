#!/usr/bin/env bash
set -euo pipefail

python3 scripts/co_tase2_full_symmetry_receipt.py \
  data/co_tase2/bns_194_268_magndata_operations.json \
  --receipt /tmp/co_tase2_full_bns_bloch_receipt.json

python3 scripts/co_tase2_published_arpes_constraints.py \
  data/co_tase2/published_arpes_constraints_2026.json \
  --receipt /tmp/co_tase2_published_arpes_constraints_receipt.json

python3 scripts/co_tase2_independent_theory_targets.py \
  data/co_tase2/independent_theory_targets_2026.json \
  --receipt /tmp/co_tase2_independent_theory_targets_receipt.json

python3 scripts/co_tase2_sah_kagome_tb.py \
  --receipt /tmp/co_tase2_sah_kagome_tb_receipt.json

python3 scripts/co_tase2_spin_space_generator_bridge.py \
  data/co_tase2/bns_194_268_magndata_operations.json \
  --receipt /tmp/co_tase2_spin_space_generator_receipt.json

python3 scripts/co_tase2_wannier90_spectral_selftest.py
python3 scripts/co_tase2_wannier_bns_covariance_selftest.py
python3 scripts/co_tase2_wannier3d_diagnostics_selftest.py
python3 scripts/co_tase2_nonabelian_topology_selftest.py
python3 scripts/co_tase2_kz_final_state_calibration_selftest.py
python3 scripts/co_tase2_arpes_observer_selftest.py

python3 -m py_compile \
  scripts/co_tase2_bloch_symmetry.py \
  scripts/co_tase2_bns_operation_audit.py \
  scripts/co_tase2_full_symmetry_receipt.py \
  scripts/co_tase2_arpes_ibw_ingest.py \
  scripts/co_tase2_arpes_observer_from_ibw.py \
  scripts/co_tase2_arpes_observer_selftest.py \
  scripts/co_tase2_arpes_peak_fit.py \
  scripts/co_tase2_arpes_forward_fit.py \
  scripts/co_tase2_published_arpes_constraints.py \
  scripts/co_tase2_independent_theory_targets.py \
  scripts/co_tase2_sah_kagome_tb.py \
  scripts/co_tase2_spin_space_generator_bridge.py \
  scripts/co_tase2_wannier90_spectral.py \
  scripts/co_tase2_wannier90_spectral_selftest.py \
  scripts/co_tase2_wannier_bns_covariance_audit.py \
  scripts/co_tase2_wannier_bns_covariance_selftest.py \
  scripts/co_tase2_wannier3d_diagnostics.py \
  scripts/co_tase2_wannier3d_diagnostics_selftest.py \
  scripts/co_tase2_nonabelian_topology.py \
  scripts/co_tase2_nonabelian_topology_selftest.py \
  scripts/co_tase2_kz_final_state_calibration.py \
  scripts/co_tase2_kz_final_state_calibration_selftest.py \
  scripts/co_tase2_dataset_download_probe.py

python3 - <<'PY'
import json
from pathlib import Path
p = Path('data/co_tase2/published_material_dft_recipe_2026.json')
d = json.loads(p.read_text())
assert d['structure_source']['space_group_number'] == 194
assert len(d['structure_source']['refined_fractional_sites']) == 5
assert d['arpes_dft_source']['code'] == 'VASP'
assert d['arpes_dft_source']['plane_wave_cutoff_ev'] == 600
assert d['arpes_dft_source']['k_mesh'] == [9, 9, 4]
assert d['reproducibility_boundary']['literal_material_hamiltonian_closed'] is False
print('PUBLISHED-MATERIAL-PRODUCER-CONTRACT: PASS')
PY

if command -v agda >/dev/null 2>&1; then
  agda -i . -i /usr/share/agda-stdlib \
    DASHI/Physics/CondensedMatter/Everything.agda
else
  echo "AGDA-NOT-AVAILABLE: umbrella kernel receipt not produced" >&2
  exit 2
fi
