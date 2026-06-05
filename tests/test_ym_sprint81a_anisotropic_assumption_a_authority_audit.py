from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    ROOT
    / "scripts"
    / "ym_sprint81a_anisotropic_assumption_a_authority_audit.py"
)


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
    return json.loads((out_dir / "ym_sprint81a_summary.json").read_text())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_sprint81a_outputs_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "audit"
    summary = run_audit(out_dir)

    authority_path = out_dir / summary["authority_table"]
    gates_path = out_dir / summary["gate_assembly_table"]
    scales_path = out_dir / summary["scale_table"]

    assert authority_path.exists()
    assert gates_path.exists()
    assert scales_path.exists()

    authorities = read_csv(authority_path)
    gates = read_csv(gates_path)

    assert any(
        row["authority_name"] == "BalabanCMP98LocalOscillationBoundForQhp"
        for row in authorities
    )
    normalized = next(
        row
        for row in authorities
        if row["authority_name"]
        == "BalabanCMP116AppendixAQhpAuthorityNormalization"
    )
    assert normalized["citation_keys"] == "CMP116;2602.0041 Appendix A"
    assert normalized["proved_in_repo"] == "False"
    assert normalized["clay_promotion"] == "False"
    assert any(
        row["gate_name"] == "LipschitzToSquaredOscillationForQhp"
        for row in gates
    )
    assert any(row["gate_name"] == "AnisotropicAssumptionA" for row in gates)


def test_sprint81a_authority_boundary(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["route_decision"] == (
        "ANISOTROPIC_ASSUMPTION_A_AUTHORITY_ASSEMBLED_NO_CLAY_PROMOTION"
    )
    assert summary["balaban_cmp98_authority_accepted"] is True
    assert (
        summary["normalized_balaban_qhp_authority_citation_surface"]
        == "CMP98/CMP116/2602.0041 Appendix A"
    )
    assert (
        summary["normalized_balaban_qhp_authority_citation_role"]
        == "external_qhp_local_oscillation_authority_surface"
    )
    assert (
        summary["normalized_balaban_qhp_authority_surface_proved_in_repo"]
        is False
    )
    assert (
        summary["normalized_balaban_qhp_authority_surface_clay_promotion"]
        is False
    )
    assert (
        summary[
            "balaban_cmp98_local_oscillation_bound_for_qhp_proved_in_repo"
        ]
        is False
    )
    assert (
        summary[
            "balaban_cmp98_local_oscillation_bound_for_qhp_authority_dependent"
        ]
        is True
    )
    assert summary["lipschitz_to_squared_oscillation_for_qhp"] is True
    assert summary["anisotropic_assumption_a_authority_conditional"] is True
    assert summary["anisotropic_assumption_a_unconditional_in_repo"] is False
    assert (
        summary[
            "fixed_finite_volume_blocked_uv_closure_authority_conditional"
        ]
        is True
    )
    assert (
        summary[
            "fixed_finite_volume_blocked_uv_closure_promoted_unconditionally"
        ]
        is False
    )


def test_sprint81a_arithmetic_and_kp_constants(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["l_block"] == 2
    assert summary["reference_k"] == 9
    assert summary["uniform_constant_form"] == "C_Q=3*C_local^2"
    assert (
        summary["qhp_per_link_bound_form"]
        == "osc_e(Q_hp)<=C_local*L^(-2k)"
    )
    assert math.isclose(summary["squared_sum_factor_at_k9"], 3 / 512)
    assert math.isclose(
        summary["ratio_at_k9_to_isotropic_4c_squared"], 3 / 2048
    )
    assert math.isclose(
        summary["percent_at_k9_relative_to_isotropic_4c_squared"],
        0.146484375,
    )
    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(summary["eta_threshold"], 4.314400833884220)
    assert math.isclose(summary["eta4_q"], 0.9271275790105094)
    assert summary["eta4_kp_arithmetic_closes"] is True
    assert math.isclose(summary["eta6_q"], 1.390691368515764)
    assert summary["eta6_kp_arithmetic_fails"] is True
    assert math.isclose(summary["eta8_q"], 1.8542551580210187)
    assert summary["eta8_kp_arithmetic_fails"] is True


def test_sprint81a_no_clay_promotion_and_next_gates(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["complete"] is False
    assert summary["effective_action_polymers_spatial_only_for_a1"] is False
    assert summary["polymer_defined_on_blocked_lattice"] is False
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["all_diameter_weighted_kp"] is False
    assert summary["mass_gap_promoted"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["next_required_gate"] == (
        "EffectiveActionPolymersSpatialOnlyForA1"
    )
    assert summary["next_required_gates"][0] == (
        "EffectiveActionPolymersSpatialOnlyForA1"
    )
