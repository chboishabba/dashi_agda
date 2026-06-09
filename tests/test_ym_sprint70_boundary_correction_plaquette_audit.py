from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint70_boundary_correction_plaquette_audit.py"


def run_audit(out_dir: Path, *args: str) -> dict[str, Any]:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            *args,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads(
        (out_dir / "ym_sprint70_boundary_leakage_summary.json").read_text(
            encoding="utf-8"
        )
    )


def read_csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_default_sun_g2_su3_route_has_no_spanning_and_no_promotion(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "default"

    checks = run_audit(out_dir)

    assert checks["suppression_mode"] == "suN-g2"
    assert checks["decomposition_mode"] == "transfer-matrix"
    assert checks["beta"] == 16.7
    assert checks["gauge_group_rank"] == 3
    assert checks["route_decision"] == "MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX"
    assert checks["bookkeeping_lambda"] == 1.0
    assert checks["correction_action_total"] == 0.0
    assert checks["correction_over_face_action"] == 0.0
    assert checks["total_leakage_factor"] == 1.0
    assert checks["total_leakage_times_4q"] == checks["eta_spatial_times_q"]
    assert checks["mixed_plaquettes_are_transfer_matrix_not_correction"] is True
    assert checks["mixed_plaquettes_are_transfer_matrix_not_correction_proved"] is True
    assert checks["temporal_measure_factorization_with_leakage_proved"] is False
    assert checks["touches_both_temporal_faces_count"] == 0
    assert checks["temporal_spanning_counterexample"] is False
    assert "transfer-matrix action includes mixed" in checks["category_precedence_contract"]
    assert checks["temporal_faces_disjoint_for_admissible_polymers"] is True
    assert checks["clay_yang_mills_promoted"] is False


def test_manual_suppression_point_zero_two_is_small_and_kp_controlled(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "manual"

    checks = run_audit(
        out_dir,
        "--suppression-mode",
        "manual",
        "--mixed-coupling-suppression",
        "0.02",
    )

    assert checks["route_decision"] == "MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX"
    assert checks["boundary_correction_small"] is True
    assert checks["mixed_coupling_suppression"] == 0.02
    assert checks["total_leakage_times_4q"] < 1.0
    assert checks["clay_yang_mills_promoted"] is False


def test_outputs_exist_and_l2_d4_contains_mixed_coupling_rows(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "outputs"

    checks = run_audit(out_dir, "--L", "2", "--dimension", "4")

    table_path = out_dir / "ym_sprint70_boundary_correction_table.csv"
    category_path = out_dir / "ym_sprint70_boundary_correction_by_category.csv"
    summary_path = out_dir / "ym_sprint70_boundary_leakage_summary.json"
    manifest_path = out_dir / "ym_sprint70_boundary_correction_manifest.json"
    assert table_path.exists()
    assert category_path.exists()
    assert summary_path.exists()
    assert manifest_path.exists()

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert "transfer-matrix action includes mixed" in manifest["category_precedence_contract"]
    assert manifest["outputs"] == {
        "plaquette_table_csv": "ym_sprint70_boundary_correction_table.csv",
        "category_summary_csv": "ym_sprint70_boundary_correction_by_category.csv",
        "summary_json": "ym_sprint70_boundary_leakage_summary.json",
    }

    plaquette_rows = read_csv_rows(table_path)
    transfer_rows = [
        row for row in plaquette_rows if row["category"] == "transfer_matrix_face_action"
    ]
    required_fields = {
        "block_id",
        "plaquette_id",
        "orientation",
        "location_class",
        "face_type",
        "wilson_action",
        "main_face_action",
        "mixed_correction_action",
        "transfer_matrix_action",
        "residual_correction_action",
        "correction_ratio",
        "touches_top_temporal_face",
        "touches_bottom_temporal_face",
        "touches_both_temporal_faces",
        "admissible_polymer",
        "passes_2p5_percent",
    }
    assert checks["L"] == 2
    assert checks["dimension"] == 4
    assert required_fields <= set(plaquette_rows[0])
    assert transfer_rows
    assert all(row["L"] == "2" and row["dimension"] == "4" for row in transfer_rows)
    assert all(row["mixed_correction_action"] == "0.0" for row in transfer_rows)
    assert all(row["residual_correction_action"] == "0.0" for row in transfer_rows)


def test_legacy_mode_preserves_old_leakage_failure(tmp_path: Path) -> None:
    out_dir = tmp_path / "legacy"

    checks = run_audit(out_dir, "--decomposition-mode", "legacy-correction")

    assert checks["decomposition_mode"] == "legacy-correction"
    assert checks["top_passes_2p5"] is False
    assert checks["bottom_passes_2p5"] is False
    assert checks["leakage_bound_passes"] is False
    assert checks["total_leakage_times_4q"] > 1.0
    assert checks["boundary_correction_small"] is False
    assert checks["route_decision"] == "BOUNDARY_CORRECTION_EXCEEDS_2P5_PERCENT"
    assert checks["clay_yang_mills_promoted"] is False


def test_prompt_command_aliases_and_safe_arithmetic(tmp_path: Path) -> None:
    out_dir = tmp_path / "prompt_command"

    checks = run_audit(
        out_dir,
        "--L",
        "2",
        "--dimension",
        "4",
        "--q",
        "0.23178189475262734",
        "--per-face-leakage-bound",
        "0.025",
        "--suppression-mode",
        "manual",
        "--mixed-coupling-suppression",
        "0.025",
    )

    assert checks["q_current"] == 0.23178189475262734
    assert checks["per_face_leakage_bound"] == 0.025
    assert math.isclose(checks["safe_three_face_leakage_factor"], 1.076890625)
    assert checks["safe_three_face_times_4q"] < 1.0
    assert checks["three_face_leakage_safe_arithmetic"] is True
    assert checks["route_decision"] == "MIXED_PLAQUETTES_ABSORBED_INTO_TRANSFER_MATRIX"
