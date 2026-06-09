from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "seam_derivation_diagnostic.py"


def run_diagnostic(tmp_path: Path, threshold: float = 0.105) -> dict[str, Any]:
    out_dir = tmp_path / "seam_diagnostic"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--width",
            "6",
            "--height",
            "5",
            "--residual-threshold",
            str(threshold),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    stdout_payload = json.loads(proc.stdout)
    file_payload = json.loads(
        (out_dir / "seam_derivation_diagnostic_summary.json").read_text(
            encoding="utf-8"
        )
    )
    assert stdout_payload == file_payload
    return stdout_payload


def test_runner_emits_finished_diagnostic_receipt(tmp_path: Path) -> None:
    payload = run_diagnostic(tmp_path)

    assert payload["benchmark"] == "seam_derivation_diagnostic"
    assert payload["status"] == "diagnostic_only"
    assert payload["claim_boundary"]["body_truth"] is False
    assert payload["claim_boundary"]["manufacturing_authority"] is False
    assert payload["claim_boundary"]["seameinit_production_promotion"] is False
    assert set(payload["receipt_hashes"]) == {
        "harness_source_hash",
        "artifact_schema_hash",
        "command_hash",
        "environment_hash",
        "artifact_hash",
    }
    assert all(len(value) == 64 for value in payload["receipt_hashes"].values())


def test_pipeline_order_is_present(tmp_path: Path) -> None:
    payload = run_diagnostic(tmp_path)

    assert payload["pipeline_order"] == [
        "input",
        "body_gate",
        "field_summary",
        "seam_cost_graph",
        "panels",
        "allowances",
        "promotion",
    ]
    assert payload["body_gate"]["gate"] == "diagnostic"
    assert payload["field_summary"]["vertex_count"] == 30
    assert payload["field_summary"]["edge_count"] > 0
    assert payload["seam_cost_graph"]["cost_hash"]


def test_selected_seams_induce_panels(tmp_path: Path) -> None:
    payload = run_diagnostic(tmp_path)

    selected = payload["seam_cost_graph"]["selected_seam_edges"]
    assert len(selected) > 0
    assert len(payload["panels"]) >= 2
    assert all(panel["topological_disk"] is True for panel in payload["panels"])
    assert all(panel["flattening"]["foldover_count"] == 0 for panel in payload["panels"])


def test_panel_residual_can_trigger_metric_correction_operator(
    tmp_path: Path,
) -> None:
    payload = run_diagnostic(tmp_path, threshold=0.01)

    shaping_ops = [
        op for panel in payload["panels"] for op in panel["shaping_ops"]
    ]
    assert shaping_ops
    assert all(op["diagnostic_only"] is True for op in shaping_ops)
    assert all(op["mdl_gain"] > 0.0 for op in shaping_ops)
    assert payload["allowances"]["asymmetric_edges"] > 0


def test_no_manufacturing_promotion(tmp_path: Path) -> None:
    payload = run_diagnostic(tmp_path)

    assert payload["promotion"]["state"] == "diagnostic_only"
    assert payload["promotion"]["severity"] == 1
    assert "synthetic_body" in payload["promotion"]["blockers"]
    assert payload["promotion"]["manufacturing_exports_generated"] is False
