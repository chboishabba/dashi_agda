from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_sprint52_material_no2cycle_replay_writes_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint52"
    source_dir.mkdir()
    source = source_dir / "ns_sprint52_material_no2cycle_summary.json"
    (source_dir / "ns_material_source_resolution.csv").write_text(
        "K,t,material_parent_id,parent_relation,child_state,parent_state,source_true_new_material,source_tracking_uncertain,source_cross_shell,source_low_shell,sigma_true_new_material,weighted_true_new_material,material_M_plus_plus\n"
        "4,0.1,p,cross_shell_parent,plus,minus,0,0,1,0,0,0,0.4\n",
        encoding="utf-8",
    )
    (source_dir / "ns_no2cycle_amplitude.csv").write_text(
        "cycle_id,K,t,minus_to_plus_mass,plus_to_minus_mass,signed_imbalance,cycle_amplitude,cycle_persistence,weighted_cycle_amplitude,plus_shell_weighted_mass,amplitude_fraction_of_plus_shell,no2cycle_proxy_fail,no2cycle_amplitude_small\n"
        "cycle_1,4,0.2,10,9,1,8,0.9,8,100,0.08,true,false\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_sprint52_material_no2cycle_artifact",
                "diagnostic_mode": "sprint52_material_parent_exponent_and_no2cycle_amplitude",
                "input_table_row_count": 2,
                "material_source_resolution_row_count": 1,
                "no2cycle_amplitude_row_count": 1,
                "source_true_new_material_total": 0.0,
                "weighted_true_new_material_total": 0.0,
                "sigma_true_new_material": 0.0,
                "material_true_new_source_absent": True,
                "material_source_beats_half_derivative": False,
                "does_material_source_gate_close": True,
                "no2cycle_candidate_count": 1,
                "no2cycle_proxy_failure_count": 1,
                "no2cycle_amplitude_small_failure_count": 0,
                "no2cycle_amplitude_small_failure_fraction": 0.0,
                "weighted_no2cycle_amplitude_total": 8.0,
                "does_no2cycle_amplitude_gate_close": False,
                "route_decision": "MATERIAL_SOURCE_GATE_CLOSED_NO2CYCLE_AMPLITUDE_BLOCKED",
                "material_source_exponent_proved": False,
                "weighted_no2cycle_amplitude_summability_proved": False,
                "clay_promotion": False,
                "navier_stokes_promotion": False,
                "promotion_status": "NO_PROMOTION_SPRINT52_MATERIAL_NO2CYCLE_DIAGNOSTIC",
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    out_dir = tmp_path / "replay"
    subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts/ns_diagnostic_harness.py"),
            "--replay-sprint52-material-no2cycle-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))

    assert checks["does_material_source_gate_close"] is True
    assert checks["does_no2cycle_amplitude_gate_close"] is False
    assert checks["route_decision"] == "MATERIAL_SOURCE_GATE_CLOSED_NO2CYCLE_AMPLITUDE_BLOCKED"
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["sprint52_material_no2cycle_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyTwoMaterialNo2CycleAuditReceipt"
    assert manifest["outputs"]["material_source_resolution_csv"] is not None
    assert manifest["outputs"]["no2cycle_amplitude_csv"] is not None
