from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint80_anisotropic_assumption_a_audit.py"


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
        (out_dir / "ym_sprint80_anisotropic_assumption_a_summary.json").read_text()
    )


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_sprint80_outputs_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "audit"
    summary = run_audit(out_dir)

    steps_path = out_dir / summary["step_table"]
    scales_path = out_dir / summary["scale_table"]

    assert steps_path.exists()
    assert scales_path.exists()

    steps = read_csv(steps_path)
    assert steps[0]["step_name"] == "SpatialOnlyQhpLinkCount"
    assert any(
        row["step_name"] == "BalabanCMP98LocalOscillationBoundForQhp"
        for row in steps
    )
    assert any(row["step_name"] == "AnisotropicAssumptionA" for row in steps)
    assert any(
        row["step_name"] == "EffectiveActionPolymersSpatialOnlyForA1"
        for row in steps
    )


def test_sprint80_reference_arithmetic(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["l_block"] == 2
    assert summary["reference_k"] == 9
    assert summary["spatial_link_multiplicity"] == 3
    assert summary["isotropic_link_multiplicity"] == 4
    assert math.isclose(
        summary["anisotropic_factor_at_k9_relative_to_c_local_squared"],
        3 / 512,
    )
    assert math.isclose(
        summary["ratio_at_k9_to_isotropic_4c_squared"],
        3 / 2048,
    )
    assert math.isclose(
        summary["percent_at_k9_relative_to_c_local_squared"],
        0.5859375,
    )
    assert math.isclose(
        summary["percent_at_k9_relative_to_isotropic_4c_squared"],
        0.146484375,
    )
    assert summary["uniform_constant_form"] == "C_Q=3*C_local^2"
    assert (
        summary["spatial_only_oscillation_sum_l2_form"]
        == "3*C_local^2*2^(-k)"
    )


def test_sprint80_eta_and_p0_floor_tracks(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert summary["eta_blocked_l2"] == 4
    assert math.isclose(summary["eta_blocked_l2_q"], 0.9271275790105094)
    assert summary["eta_blocked_l2_kp_arithmetic_closes"] is True
    assert summary["eta_fine_lattice_spatial"] == 6
    assert math.isclose(
        summary["eta_fine_lattice_spatial_q"], 1.390691368515764
    )
    assert summary["eta_fine_lattice_spatial_kp_arithmetic_fails"] is True
    assert summary["eta_generic_4d"] == 8
    assert math.isclose(summary["eta_generic_4d_q"], 1.8542551580210187)
    assert summary["eta_generic_4d_kp_arithmetic_fails"] is True

    assert summary["p0_floor_track_explicit"] is True
    assert math.isclose(summary["source_floor"], 3.079)
    assert math.isclose(summary["p0_at_k8"], 3.057)
    assert math.isclose(summary["p0_at_k9"], 3.124)
    assert summary["p0_k8_below_source_floor"] is True
    assert summary["p0_k9_above_source_floor"] is True
    assert summary["k_start_spacetime_floor"] == 9


def test_sprint80_fail_closed(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["route_decision"] == (
        "ANISOTROPIC_ASSUMPTION_A_PROOF_PLAN_READY_FAIL_CLOSED"
    )
    assert summary["three_step_proof_plan_recorded"] is True
    assert summary["conditional_volume_arithmetic_closes"] is True
    assert summary["balaban_cmp98_local_oscillation_bound_for_qhp"] is False
    assert summary["lipschitz_to_squared_oscillation_for_qhp"] is False
    assert summary["anisotropic_assumption_a"] is False
    assert summary["effective_action_polymers_spatial_only_for_a1"] is False
    assert summary["fixed_finite_volume_blocked_uv_closure_promoted"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["next_required_lemmas"][0] == (
        "BalabanCMP98LocalOscillationBoundForQhp"
    )
