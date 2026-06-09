from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint79_effective_action_support_audit.py"

SUPPORT_FIELDS = [
    "polymer_id",
    "rg_scale_k",
    "source_term_class",
    "contains_temporal_link",
    "contains_mixed_temporal_spatial_plaquette",
    "absorbed_into_transfer_matrix",
    "residual_effective_action_term",
    "spatial_support_only",
    "blocked_lattice_polymer",
    "fine_lattice_eta",
    "blocked_lattice_eta",
    "kp_entropy_used",
    "route_decision",
]


def run_audit(out_dir: Path) -> dict[str, Any]:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(
        (out_dir / "ym_sprint79_effective_action_spatial_a1_summary.json").read_text()
    )


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_sprint79_writes_requested_artifacts_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "sprint79"
    summary = run_audit(out_dir)

    support_path = out_dir / "ym_sprint79_effective_action_support_table.csv"
    entropy_path = out_dir / "ym_sprint79_kp_graph_entropy_table.csv"
    summary_path = out_dir / "ym_sprint79_effective_action_spatial_a1_summary.json"

    assert support_path.exists()
    assert entropy_path.exists()
    assert summary_path.exists()
    assert summary["support_table"] == support_path.name
    assert summary["kp_graph_entropy_table"] == entropy_path.name

    rows = read_csv(support_path)
    assert rows
    assert list(rows[0].keys()) == SUPPORT_FIELDS


def test_sprint79_support_audit_is_fail_closed_until_a1_and_blocked_graph(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "sprint79"
    summary = run_audit(out_dir)
    rows = read_csv(out_dir / "ym_sprint79_effective_action_support_table.csv")

    residual = [row for row in rows if row["residual_effective_action_term"] == "True"]
    assert residual
    assert any(row["spatial_support_only"] == "False" for row in residual)
    assert any(row["blocked_lattice_polymer"] == "False" for row in residual)
    assert any(row["kp_entropy_used"] == "6" for row in residual)

    assert summary["effective_action_polymers_spatial_only_for_a1"] is False
    assert summary["polymer_defined_on_blocked_lattice"] is False
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["pass_condition_met"] is False
    assert summary["fail_condition_temporal_support_unproved_or_present"] is True
    assert summary["fail_condition_kp_graph_fine_lattice_eta6"] is True
    assert summary["route_decision"] == "ANISOTROPIC_KP_ROUTE_BLOCKED"


def test_sprint79_entropy_constants_and_route_decisions(tmp_path: Path) -> None:
    out_dir = tmp_path / "sprint79"
    summary = run_audit(out_dir)
    rows = read_csv(out_dir / "ym_sprint79_kp_graph_entropy_table.csv")

    assert summary["fine_lattice_eta"] == 6
    assert math.isclose(summary["fine_lattice_eta_q"], 1.390691368515764)
    assert summary["fine_lattice_eta_blocks_kp"] is True
    assert summary["blocked_lattice_eta"] == 4
    assert math.isclose(summary["blocked_lattice_eta_q"], 0.9271275790105094)
    assert summary["blocked_l2_kp_arithmetic_closes"] is True
    assert summary["generic_4d_eta"] == 8
    assert math.isclose(summary["generic_4d_eta_q"], 1.8542551580210187)

    decisions = {row["route_decision"] for row in rows}
    assert "KP_GRAPH_IS_FINE_LATTICE_ETA6_BLOCKED" in decisions
    assert "KP_GRAPH_IS_BLOCKED_L2_ETA4_CONFIRMED" in decisions
    assert "ANISOTROPIC_KP_ROUTE_BLOCKED" in decisions
