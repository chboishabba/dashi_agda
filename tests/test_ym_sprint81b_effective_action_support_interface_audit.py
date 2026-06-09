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
    ROOT / "scripts" / "ym_sprint81b_effective_action_support_interface_audit.py"
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
    return json.loads((out_dir / "ym_sprint81b_summary.json").read_text())


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_sprint81b_outputs_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "audit"
    summary = run_audit(out_dir)

    interface_path = out_dir / summary["interface_table"]
    gate_path = out_dir / summary["gate_table"]

    assert interface_path.exists()
    assert gate_path.exists()

    interfaces = read_csv(interface_path)
    gates = read_csv(gate_path)

    assert any(row["interface_name"] == "BalabanEffectiveAction" for row in interfaces)
    assert any(row["interface_name"] == "Polymer" for row in interfaces)
    assert any(row["interface_name"] == "PolymerIn" for row in interfaces)
    assert any(row["interface_name"] == "TemporalLink" for row in interfaces)
    assert any(row["interface_name"] == "SpatialLink" for row in interfaces)
    assert any(row["interface_name"] == "SpatialSupport" for row in interfaces)
    assert any(
        row["interface_name"] == "ActivityDependsOnlyOnLinksInsidePolymer"
        for row in interfaces
    )
    assert any(
        row["gate_name"] == "EffectiveActionPolymersSpatialOnlyForA1"
        for row in gates
    )
    assert any(row["gate_name"] == "KPEntropyAtBlockedScaleL2" for row in gates)


def test_sprint81b_support_interface_fail_closed(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["route_decision"] == (
        "EFFECTIVE_ACTION_SUPPORT_INTERFACE_DEFINED_BALABAN_AUTHORITY_CONDITIONAL"
    )
    assert summary["complete"] is False
    assert summary["support_interface_defined"] is True
    assert summary["spatial_only_bridge_defined"] is True
    assert summary["balaban_effective_action_carrier_defined"] is True
    assert summary["polymer_carrier_defined"] is True
    assert summary["polymer_in_relation_defined"] is True
    assert summary["link_kind_temporal_spatial_defined"] is True
    assert summary["temporal_link_predicate_defined"] is True
    assert summary["spatial_link_predicate_defined"] is True
    assert summary["polymer_support_defined"] is True
    assert summary["spatial_support_predicate_defined"] is True
    assert summary["residual_effective_action_term_defined"] is True
    assert summary["activity_depends_only_on_links_inside_polymer_defined"] is True
    assert summary["temporal_measure_factorization_lambda_one_reconciled"] is True
    assert summary["defined_on_blocked_l2_spatial_graph_defined"] is True
    assert summary["effective_action_polymers_spatial_only_for_a1"] is False
    assert (
        summary["effective_action_polymers_spatial_only_for_a1_authority_conditional"]
        is True
    )
    assert summary["cmp116_equations_2_12_2_13_authority_available"] is True
    assert summary["cmp116_equations_2_12_2_13_derived_in_repo"] is False
    assert summary["polymer_defined_on_blocked_lattice"] is False
    assert summary["polymer_defined_on_blocked_lattice_authority_conditional"] is True
    assert summary["kp_entropy_at_blocked_scale_l2"] is False
    assert summary["kp_entropy_at_blocked_scale_l2_authority_conditional"] is True
    assert summary["all_diameter_weighted_kp"] is False
    assert summary["all_diameter_weighted_kp_authority_conditional"] is True
    assert summary["eta4_earned_authority_conditional"] is True
    assert summary["eta4_earned_unconditional"] is False
    assert summary["mass_gap_promoted"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint81b_kp_guardrails(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(summary["eta_threshold"], 4.314400833884220)
    assert math.isclose(summary["eta4_q"], 0.9271275790105094)
    assert summary["eta4_kp_arithmetic_closes"] is True
    assert math.isclose(summary["eta6_q"], 1.390691368515764)
    assert summary["eta6_kp_arithmetic_fails"] is True
    assert math.isclose(summary["eta8_q"], 1.8542551580210187)
    assert summary["eta8_kp_arithmetic_fails"] is True


def test_sprint81b_next_required_support_interface(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["next_required_gate"] == "ResidualEffectiveActionSpatialSupportEvidence"
    assert summary["next_required_support_interface"] == [
        "BalabanEffectiveAction",
        "Polymer",
        "PolymerIn",
        "LinkKindTemporalSpatial",
        "TemporalLink",
        "SpatialLink",
        "PolymerSupport",
        "SpatialSupport",
        "ResidualEffectiveActionTerm",
        "ActivityDependsOnlyOnLinksInsidePolymer",
        "TemporalMeasureFactorizationLambdaOneReconciled",
        "DefinedOnBlockedL2SpatialGraph",
    ]
    assert summary["next_required_kp_gates"][:4] == [
        "ResidualEffectiveActionSpatialSupportEvidence",
        "EffectiveActionPolymersSpatialOnlyForA1",
        "PolymerDefinedOnBlockedLattice",
        "KPEntropyAtBlockedScaleL2",
    ]
