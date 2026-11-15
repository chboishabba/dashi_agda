from __future__ import annotations

import importlib.util
import json
import subprocess
import sys

import pytest
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "seam_derivation_diagnostic.py"

SPEC = importlib.util.spec_from_file_location("seam_derivation_diagnostic", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
SEAM = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SEAM
SPEC.loader.exec_module(SEAM)


def run_diagnostic(
    tmp_path: Path,
    threshold: float = 0.105,
    *,
    max_reprojection_distance: float = 0.02,
    mean_reprojection_distance: float = 0.01,
    min_edge_retention_ratio: float = 0.99,
) -> dict[str, Any]:
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
            "--max-reprojection-distance",
            str(max_reprojection_distance),
            "--mean-reprojection-distance",
            str(mean_reprojection_distance),
            "--min-edge-retention-ratio",
            str(min_edge_retention_ratio),
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
        "reprojection_gate",
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

def test_reprojection_quality_gate_reports_compatible_meshes(
    tmp_path: Path,
) -> None:
    payload = run_diagnostic(tmp_path)
    gate = payload["reprojection_gate"]

    assert gate["passed"] is True
    assert 0.0 < gate["max_distance"] <= gate["thresholds"]["max_distance"]
    assert 0.0 < gate["mean_distance"] <= gate["thresholds"]["mean_distance"]
    assert gate["edge_retention_ratio"] == 1.0
    assert gate["retained_edges"] == gate["source_edge_count"]
    assert len(gate["vertex_mapping_hash"]) == 64
    assert (
        payload["seam_cost_graph"]["selected_source_seam_edges"]
        == payload["seam_cost_graph"]["selected_target_seam_edges"]
    )


def test_reprojection_distance_gate_fails_loudly(tmp_path: Path) -> None:
    out_dir = tmp_path / "too_far"
    proc = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--width",
            "6",
            "--height",
            "5",
            "--max-reprojection-distance",
            "0.000001",
            "--mean-reprojection-distance",
            "0.000001",
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert proc.returncode != 0
    assert "incompatible source/target meshes" in proc.stderr
    assert "max_distance=" in proc.stderr
    assert "mean_distance=" in proc.stderr
    assert not (out_dir / "seam_derivation_diagnostic_summary.json").exists()


def test_edge_retention_gate_fails_loudly() -> None:
    source_vertices = [
        SEAM.Vertex(0, 0, 0, 0.0, 0.0, 0.0),
        SEAM.Vertex(1, 1, 0, 1.0, 0.0, 0.0),
        SEAM.Vertex(2, 2, 0, 2.0, 0.0, 0.0),
    ]
    target_vertices = list(source_vertices)
    source_edges = [
        SEAM.Edge(0, 0, 1, "horizontal"),
        SEAM.Edge(1, 1, 2, "horizontal"),
    ]
    target_edges = [
        SEAM.Edge(0, 0, 1, "horizontal"),
    ]

    quality, _ = SEAM.reprojection_quality(
        source_vertices,
        source_edges,
        target_vertices,
        target_edges,
    )

    assert quality.max_distance == 0.0
    assert quality.mean_distance == 0.0
    assert quality.edge_retention_ratio == 0.5

    with pytest.raises(
        SEAM.ReprojectionCompatibilityError,
        match="edge_retention_ratio=",
    ):
        SEAM.require_reprojection_compatible(
            quality,
            max_distance=0.01,
            mean_distance=0.01,
            min_edge_retention_ratio=0.75,
        )

