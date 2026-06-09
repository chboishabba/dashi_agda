from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ns_sprint83_hminus_half_canonical_lane_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "sprint83_ns"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ns_sprint83_hminus_half_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_sprint83_ns_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint83_hminus_half_canonical_lane_audit"
    assert (out_dir / "ns_sprint83_hminus_half_source_surface_table.csv").exists()
    assert (out_dir / "ns_sprint83_hminus_half_gate_table.csv").exists()
    assert (out_dir / "ns_sprint83_hminus_half_summary.json").exists()

    source_rows = read_csv(out_dir / "ns_sprint83_hminus_half_source_surface_table.csv")
    gate_rows = read_csv(out_dir / "ns_sprint83_hminus_half_gate_table.csv")

    assert {row["surface_name"] for row in source_rows} == {
        "HminusHalfGateDecisionPivot",
        "NonCircularKStarDriftBoundTarget",
        "TailRestrictedThetaDiagnostic",
        "ThetaTailToBKMBridge",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "HminusHalfUniformAbsorptionGate",
        "NonCircularKStarDriftBound",
        "ThetaPreservationAtDangerShell",
        "ThetaTailToBKMOrSerrinContinuation",
        "ClayNavierStokesPromoted",
    }


def test_sprint83_ns_records_canonical_open_route(tmp_path: Path) -> None:
    _out_dir, summary = run_audit(tmp_path)

    assert summary["complete"] is False
    assert summary["route_decision"] == "NS_HMINUS_HALF_CANONICAL_LANE_OPEN"
    assert summary["hminus_half_source_surface"] is True
    assert summary["kstar_source_surface"] is True
    assert summary["theta_source_surface"] is True
    assert summary["bkm_source_surface"] is True
    assert summary["all_required_source_surfaces_present"] is True
    assert summary["next_required_gate"] == "HminusHalfUniformAbsorptionGate"


def test_sprint83_ns_keeps_proofs_and_clay_promotion_false(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint83_hminus_half_gate_table.csv")

    assert summary["hminus_half_uniform_absorption_proved_in_repo"] is False
    assert summary["non_circular_kstar_drift_bound_proved_in_repo"] is False
    assert summary["theta_preservation_proved_in_repo"] is False
    assert summary["bkm_or_serrin_continuation_discharged_in_repo"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True

    clay_gate = next(
        row for row in gate_rows if row["gate_name"] == "ClayNavierStokesPromoted"
    )
    assert clay_gate["status"] == "FALSE_NO_PROMOTION"
    assert clay_gate["proved_in_repo"] == "False"
    assert clay_gate["clay_promotion"] == "False"


def test_sprint83_ns_source_rows_are_present_but_not_promoted(
    tmp_path: Path,
) -> None:
    out_dir, summary = run_audit(tmp_path)
    rows = read_csv(out_dir / "ns_sprint83_hminus_half_source_surface_table.csv")

    assert summary["route_decision"] == "NS_HMINUS_HALF_CANONICAL_LANE_OPEN"
    assert all(row["present_in_repo"] == "True" for row in rows)
    assert all(row["proved_in_repo"] == "False" for row in rows)
    assert all(
        row["route_decision"] == "NS_HMINUS_HALF_CANONICAL_LANE_OPEN"
        for row in rows
    )
