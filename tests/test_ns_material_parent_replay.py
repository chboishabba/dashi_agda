from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


FIELDNAMES = [
    "time",
    "K_child",
    "M_plus_plus_material",
    "source_true_new",
    "source_tracking_uncertain",
    "source_cross_shell",
    "source_low_shell_injection",
    "source_total_material",
    "weighted_true_new",
    "weighted_tracking_uncertain",
    "weighted_cross_shell",
    "weighted_low_shell_injection",
    "weighted_total_material",
    "sigma_true_new_fit",
    "sigma_tracking_uncertain_fit",
    "sigma_cross_shell_fit",
    "sigma_low_shell_fit",
    "sigma_total_material_fit",
    "route_status",
]


def test_material_parent_replay_writes_contract_manifest_and_checks(tmp_path: Path) -> None:
    source = tmp_path / "gpu_ns_material_parent_summary.csv"
    rows = [
        {
            "time": "0.1",
            "K_child": "6",
            "M_plus_plus_material": "0.42",
            "source_true_new": "0.015625",
            "source_tracking_uncertain": "0.001",
            "source_cross_shell": "0.0005",
            "source_low_shell_injection": "0.00025",
            "source_total_material": "0.017375",
            "weighted_true_new": "0.125",
            "weighted_tracking_uncertain": "0.008",
            "weighted_cross_shell": "0.004",
            "weighted_low_shell_injection": "0.002",
            "weighted_total_material": "0.139",
            "sigma_true_new_fit": "0.75",
            "sigma_tracking_uncertain_fit": "0.25",
            "sigma_cross_shell_fit": "0.2",
            "sigma_low_shell_fit": "0.1",
            "sigma_total_material_fit": "0.7",
            "route_status": "MATERIAL_PARENT_REPAIRS_NEW_SOURCE_DIAGNOSTIC_ONLY",
        },
        {
            "time": "0.1",
            "K_child": "7",
            "M_plus_plus_material": "0.4",
            "source_true_new": "0.0078125",
            "source_tracking_uncertain": "0.0005",
            "source_cross_shell": "0.00025",
            "source_low_shell_injection": "0.000125",
            "source_total_material": "0.0086875",
            "weighted_true_new": "0.0883883476",
            "weighted_tracking_uncertain": "0.0056568542",
            "weighted_cross_shell": "0.0028284271",
            "weighted_low_shell_injection": "0.0014142136",
            "weighted_total_material": "0.0982878425",
            "sigma_true_new_fit": "0.75",
            "sigma_tracking_uncertain_fit": "0.25",
            "sigma_cross_shell_fit": "0.2",
            "sigma_low_shell_fit": "0.1",
            "sigma_total_material_fit": "0.7",
            "route_status": "MATERIAL_PARENT_REPAIRS_NEW_SOURCE_DIAGNOSTIC_ONLY",
        },
    ]
    with source.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)

    out_dir = tmp_path / "replay"
    subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts/ns_diagnostic_harness.py"),
            "--replay-material-parent-summary",
            str(source),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
    )

    replay_csv = out_dir / "ns_material_parent_summary.csv"
    summary_json = out_dir / "ns_material_parent_summary.json"
    checks_json = out_dir / "ns_diagnostic_checks.json"
    manifest_json = out_dir / "ns_diagnostic_manifest.json"

    replay_rows = list(csv.DictReader(replay_csv.open(newline="", encoding="utf-8")))
    summary = json.loads(summary_json.read_text(encoding="utf-8"))
    checks = json.loads(checks_json.read_text(encoding="utf-8"))
    manifest = json.loads(manifest_json.read_text(encoding="utf-8"))

    assert len(replay_rows) == 2
    assert summary["material_parent_summary_row_count"] == 2
    assert summary["sigma_true_new"] == 0.75
    assert summary["sigma_tracking_uncertain"] == 0.25
    assert summary["material_parent_route_status"] == "MATERIAL_PARENT_REPAIRS_NEW_SOURCE_DIAGNOSTIC_ONLY"
    assert checks["material_parent_replay_reruns_shell_packets"] is False
    assert checks["clay_promotion"] is False
    assert manifest["receipt_alignment"] == "DASHI.Physics.Closure.ClaySprintFortyNineMaterialParentReplayReceipt"
    assert manifest["navier_stokes_promotion"] is False
