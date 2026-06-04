from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def test_ternary_cross_shell_replay_writes_contract_manifest_and_checks(tmp_path: Path) -> None:
    source_dir = tmp_path / "gpu_sprint50"
    source_dir.mkdir()
    source = source_dir / "ns_ternary_cross_shell_summary.json"
    matrix = source_dir / "ns_full_ternary_transition_matrix.csv"
    decomp = source_dir / "ns_cross_shell_source_decomposition.csv"

    matrix_rows = [
        {
            "source_kind": "cross_shell",
            "child_state": "plus",
            "parent_state": "zero",
            "transition_mass": "5",
            "weighted_child_mass": "20",
            "row_count": "1",
        }
    ]
    with matrix.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(matrix_rows[0]))
        writer.writeheader()
        writer.writerows(matrix_rows)
    decomp.write_text(
        "source_kind,parent_state,child_state,transition_mass,weighted_child_mass,bt_distance_proxy_min,bt_distance_proxy_max,bt_distance_proxy_mass_weighted_mean,row_count\n"
        "cross_shell,zero,plus,5,20,3,3,3,1\n",
        encoding="utf-8",
    )
    source.write_text(
        json.dumps(
            {
                "contract": "ns_ternary_cross_shell_artifact",
                "diagnostic_mode": "sprint50_full_ternary_cross_shell_from_material_parent_table",
                "matrix_entry_count": 63,
                "source_decomposition_entry_count": 54,
                "weighted_cross_plus_from_minus": 1.0,
                "weighted_cross_plus_from_zero": 20.0,
                "weighted_cross_plus_from_plus": 2.0,
                "sigma_cross_from_minus": 0.043478260869565216,
                "sigma_cross_from_zero": 0.8695652173913043,
                "sigma_cross_from_plus": 0.08695652173913043,
                "dominant_red_source_state": "zero",
                "dominant_red_source_kind": "cross_shell",
                "route_decision": "CROSS_PLUS_FROM_ZERO_DOMINATES",
                "BT_distance_proxy": "abs(K_child - K_parent)",
                "classification_field_used_for_source_kind": False,
                "full_ternary_matrix_available": True,
                "adjacent_only_theorem_sufficient": False,
                "cross_shell_summability_proved": False,
                "bt_distance_decay_theorem_proved": False,
                "clay_promotion": False,
                "navier_stokes_promotion": False,
                "promotion_status": "NO_PROMOTION_TERNARY_CROSS_SHELL_DIAGNOSTIC",
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
            "--replay-ternary-cross-shell-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    replay_summary = json.loads((out_dir / "ns_ternary_cross_shell_summary.json").read_text(encoding="utf-8"))
    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    manifest = json.loads((out_dir / "ns_diagnostic_manifest.json").read_text(encoding="utf-8"))
    replay_matrix = list(csv.DictReader((out_dir / "ns_full_ternary_transition_matrix.csv").open(newline="", encoding="utf-8")))

    assert replay_summary["route_decision"] == "CROSS_PLUS_FROM_ZERO_DOMINATES"
    assert checks["weighted_cross_plus_from_zero"] == 20.0
    assert checks["sigma_cross_from_zero"] == 0.8695652173913043
    assert checks["dominant_red_source_state"] == "zero"
    assert checks["dominant_red_source_kind"] == "cross_shell"
    assert checks["material_parent_lineage_recomputed"] is False
    assert checks["ternary_cross_shell_replay_promotes"] is False
    assert checks["clay_promotion"] is False
    assert checks["navier_stokes_promotion"] is False
    assert checks["pass"] is False
    assert replay_matrix[0]["weighted_child_mass"] == "20"
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFiftyFullTernaryCrossShellAuditReceipt"
    assert manifest["outputs"]["cross_shell_source_decomposition_csv"] is not None
    assert manifest["navier_stokes_promotion"] is False
