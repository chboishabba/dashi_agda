from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ns_sprint86_kstar_hhalf_obstruction_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "ns_sprint86"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ns_sprint86_kstar_hhalf_obstruction_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_ns_sprint86_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint86_kstar_hhalf_obstruction_audit"
    assert (
        out_dir / "ns_sprint86_kstar_hhalf_obstruction_source_surface_table.csv"
    ).exists()
    assert (out_dir / "ns_sprint86_kstar_hhalf_obstruction_gate_table.csv").exists()
    assert (out_dir / "ns_sprint86_kstar_hhalf_obstruction_summary.json").exists()

    source_rows = read_csv(
        out_dir / "ns_sprint86_kstar_hhalf_obstruction_source_surface_table.csv"
    )
    gate_rows = read_csv(out_dir / "ns_sprint86_kstar_hhalf_obstruction_gate_table.csv")

    assert {row["surface_name"] for row in source_rows} == {
        "Sprint86KStarHHalfTailObstruction",
        "Sprint84OneSobolevGapTarget",
        "NonCircularObstruction",
        "NegativeSobolevDangerShell",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "QhpHighHighProductEstimate",
        "QhpTailSmallnessAtDangerShell",
        "KStarAdmissibilityAloneControlsHHalfTail",
        "KStarAdmissibilityAloneObstruction",
        "EpsilonBelowOneCoefficient",
        "HminusHalfHighHighDefectTheorem",
        "ClayNavierStokesPromoted",
    }


def test_ns_sprint86_records_kstar_hhalf_obstruction_route(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["complete"] is False
    assert summary["route_decision"] == "NS_SPRINT86_KSTAR_HHALF_OBSTRUCTION_OPEN"
    assert summary["next_required_gate"] == "QhpTailSmallnessAtDangerShell"
    assert summary["open_obligations"] == [
        "QhpHighHighProductEstimate",
        "QhpTailSmallnessAtDangerShell",
        "KStarAdmissibilityAloneControlsHHalfTail",
        "EpsilonBelowOneCoefficient",
        "HminusHalfHighHighDefectTheorem",
    ]


def test_ns_sprint86_surfaces_present_and_obstruction_recorded(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    rows = read_csv(
        out_dir / "ns_sprint86_kstar_hhalf_obstruction_source_surface_table.csv"
    )

    assert summary["sprint86_kstar_hhalf_tail_obstruction_surface"] is True
    assert summary["sprint84_one_sobolev_gap_target_surface"] is True
    assert summary["non_circular_obstruction_surface"] is True
    assert summary["negative_sobolev_danger_shell_surface"] is True
    assert summary["all_required_source_surfaces_present"] is True
    assert all(row["present_in_repo"] == "True" for row in rows)
    assert summary["qhp_formal_commutation_package_recorded"] is True
    assert summary["kstar_admissibility_alone_obstruction_recorded"] is True


def test_ns_sprint86_forbids_hidden_regularities_and_promotions(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint86_kstar_hhalf_obstruction_gate_table.csv")

    assert summary["qhp_high_high_product_estimate_derived_in_repo"] is False
    assert summary["qhp_tail_smallness_at_danger_shell_derived_in_repo"] is False
    assert summary["kstar_admissibility_alone_controls_hhalf_tail_derived_in_repo"] is False
    assert summary["h_one_half_tail_assumed_by_allowed_proof"] is False
    assert summary["serrin_or_bkm_assumed_by_allowed_proof"] is False
    assert summary["stronger_regularity_assumed_by_allowed_proof"] is False
    assert summary["epsilon_below_one_coefficient_derived_in_repo"] is False
    assert summary["hminus_half_high_high_defect_theorem_derived_in_repo"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True
    assert all(row["clay_promotion"] == "False" for row in gate_rows)

