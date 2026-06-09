from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ns_sprint87_absorption_scaling_audit.py")


def run_audit(tmp_path: Path) -> tuple[Path, dict]:
    out_dir = tmp_path / "ns_sprint87_absorption_scaling"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)],
        check=True,
        cwd=Path.cwd(),
    )
    summary = json.loads(
        (out_dir / "ns_sprint87_absorption_scaling_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def test_ns_sprint87_outputs_and_schema(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)

    assert summary["contract"] == "ns_sprint87_absorption_scaling_audit"
    assert (out_dir / "ns_sprint87_absorption_scaling_source_surface_table.csv").exists()
    assert (out_dir / "ns_sprint87_absorption_scaling_gate_table.csv").exists()
    assert (out_dir / "ns_sprint87_absorption_scaling_summary.json").exists()

    source_rows = read_csv(
        out_dir / "ns_sprint87_absorption_scaling_source_surface_table.csv"
    )
    gate_rows = read_csv(out_dir / "ns_sprint87_absorption_scaling_gate_table.csv")

    assert {row["surface_name"] for row in source_rows} >= {
        "Sprint87AbsorptionScalingAudit",
        "Sprint86KStarHHalfTailObstruction",
        "Sprint84OneSobolevGapTarget",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "NuInverseAbsorptionLaw",
        "NuFourThirdsInverseAbsorptionLaw",
        "NuSquaredInverseAbsorptionLaw",
        "RequiredScalarAbsorptionCondition",
        "UnconditionalAbsorptionClosed",
        "ClayNavierStokesPromoted",
    }


def test_ns_sprint87_records_three_absorption_scaling_laws(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint87_absorption_scaling_gate_table.csv")
    gates_by_name = {row["gate_name"]: row for row in gate_rows}

    assert summary["absorption_scaling_laws_recorded"] == [
        "nu^-1",
        "nu^-4/3",
        "nu^-2",
    ]
    assert summary["nu_inverse_absorption_law_recorded"] is True
    assert summary["nu_four_thirds_inverse_absorption_law_recorded"] is True
    assert summary["nu_squared_inverse_absorption_law_recorded"] is True

    assert gates_by_name["NuInverseAbsorptionLaw"]["scaling_law"] == "nu^-1"
    assert gates_by_name["NuFourThirdsInverseAbsorptionLaw"]["scaling_law"] == "nu^-4/3"
    assert gates_by_name["NuSquaredInverseAbsorptionLaw"]["scaling_law"] == "nu^-2"


def test_ns_sprint87_required_scalar_condition_named(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint87_absorption_scaling_gate_table.csv")
    gates_by_name = {row["gate_name"]: row for row in gate_rows}

    assert (
        summary["required_scalar_condition_name"]
        == "RequiredScalarAbsorptionCondition"
    )
    assert summary["required_scalar_condition_named"] is True
    assert gates_by_name["RequiredScalarAbsorptionCondition"][
        "next_required_input"
    ] == "derive scalar absorption inequality uniformly in the NS route"


def test_ns_sprint87_fails_closed_without_clay_promotion(tmp_path: Path) -> None:
    out_dir, summary = run_audit(tmp_path)
    gate_rows = read_csv(out_dir / "ns_sprint87_absorption_scaling_gate_table.csv")
    gates_by_name = {row["gate_name"]: row for row in gate_rows}

    assert summary["complete"] is False
    assert summary["unconditional_absorption_closed"] is False
    assert summary["clay_navier_stokes_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True
    assert gates_by_name["UnconditionalAbsorptionClosed"]["proved_in_repo"] == "False"
    assert gates_by_name["ClayNavierStokesPromoted"]["clay_promotion"] == "False"
    assert all(row["clay_promotion"] == "False" for row in gate_rows)
