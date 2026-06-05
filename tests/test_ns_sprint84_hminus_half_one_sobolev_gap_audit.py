from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ns_sprint84_hminus_half_one_sobolev_gap_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "sprint84_ns"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ns_sprint84_one_sobolev_gap_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_sprint84_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint84_hminus_half_one_sobolev_gap_audit"
    assert (out_dir / "ns_sprint84_one_sobolev_gap_source_surface_table.csv").exists()
    assert (out_dir / "ns_sprint84_one_sobolev_gap_gate_table.csv").exists()
    assert (out_dir / "ns_sprint84_one_sobolev_gap_summary.json").exists()

    source_rows = read_csv(out_dir / "ns_sprint84_one_sobolev_gap_source_surface_table.csv")
    gate_rows = read_csv(out_dir / "ns_sprint84_one_sobolev_gap_gate_table.csv")

    assert {row["surface_name"] for row in source_rows} == {
        "OneSobolevGapTarget",
        "NegativeSobolevDangerShell",
        "CanonicalHminusLane",
        "QhpNSCommutationPackage",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "FormalQhpMapForNSBridge",
        "QhpDangerShellProjectionCommutation",
        "QhpKStarCutoffCommutation",
        "QhpTailFluxPairingCommutation",
        "EpsilonBelowOneCoefficient",
        "ClayNavierStokesPromoted",
    }


def test_sprint84_records_highest_alpha_open_route(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["complete"] is False
    assert (
        summary["route_decision"]
        == "NS_HMINUS_HALF_ONE_SOBOLEV_GAP_QHP_OPEN"
    )
    assert summary["next_required_gate"] == "AnalyticAbsorptionFromQhpCommutation"
    assert summary["highest_alpha_ns_path"][:4] == [
        "FormalQhpMapForNSBridge",
        "QhpDangerShellProjectionCommutation",
        "QhpKStarCutoffCommutation",
        "QhpTailFluxPairingCommutation",
    ]
    assert summary["highest_alpha_ns_path"][4:6] == [
        "EpsilonBelowOneCoefficient",
        "HminusHalfHighHighDefectTheorem",
    ]


def test_sprint84_source_surfaces_present_but_unproved(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    rows = read_csv(out_dir / "ns_sprint84_one_sobolev_gap_source_surface_table.csv")

    assert summary["one_sobolev_gap_target_surface"] is True
    assert summary["negative_sobolev_danger_shell_surface"] is True
    assert summary["canonical_hminus_lane_surface"] is True
    assert summary["qhp_ns_commutation_package_surface"] is True
    assert summary["all_required_source_surfaces_present"] is True
    assert all(row["present_in_repo"] == "True" for row in rows)
    assert {
        row["surface_name"]: row["proved_in_repo"]
        for row in rows
    } == {
        "OneSobolevGapTarget": "False",
        "NegativeSobolevDangerShell": "False",
        "CanonicalHminusLane": "False",
        "QhpNSCommutationPackage": "True",
    }


def test_sprint84_keeps_qhp_and_clay_flags_false(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint84_one_sobolev_gap_gate_table.csv")

    assert summary["one_sobolev_step_gap_target_recorded"] is True
    assert summary["one_sobolev_step_gap_closed_here"] is False
    assert summary["littlewood_paley_high_high_estimate_recorded"] is True
    assert summary["littlewood_paley_reaches_h_three_four_squared"] is True
    assert summary["needed_h_three_half_tail_dissipation_recorded"] is True
    assert "H^{3/4}" in summary["littlewood_paley_estimate"]
    assert "H^{3/2}" in summary["needed_tail_dissipation_estimate"]
    assert summary["formal_qhp_map_available_for_ns_bridge"] is True
    assert summary["qhp_commutes_with_danger_shell_projection"] is True
    assert summary["qhp_commutes_with_kstar_cutoff"] is True
    assert summary["qhp_commutes_with_tail_flux_pairing"] is True
    assert summary["qhp_commutation_formal_witness_recorded"] is True
    assert summary["qhp_commutation_proved_here"] is False
    assert (
        summary["ns1_hminus_half_high_high_defect_theorem_proved_here"]
        is False
    )
    assert summary["ns2_non_circular_kstar_drift_is_downstream"] is True
    assert summary["ns3_edge_influx_theta_preservation_is_downstream"] is True
    assert summary["ns4_theta_tail_to_bkm_continuation_is_downstream"] is True
    assert summary["epsilon_below_one_coefficient_proved_here"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True

    clay_gate = next(
        row for row in gate_rows if row["gate_name"] == "ClayNavierStokesPromoted"
    )
    assert clay_gate["status"] == "FALSE_NO_PROMOTION"
    assert clay_gate["clay_promotion"] == "False"
