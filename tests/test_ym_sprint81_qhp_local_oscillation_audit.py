from __future__ import annotations

import csv
import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint81_qhp_local_oscillation_audit.py"


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
        (out_dir / "ym_sprint81_qhp_local_oscillation_summary.json").read_text()
    )


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def test_sprint81_outputs_and_schema(tmp_path: Path) -> None:
    out_dir = tmp_path / "audit"
    summary = run_audit(out_dir)

    missing_path = out_dir / summary["missing_input_table"]
    attempts_path = out_dir / summary["attempt_table"]
    scales_path = out_dir / summary["scale_table"]

    assert missing_path.exists()
    assert attempts_path.exists()
    assert scales_path.exists()

    missing = read_csv(missing_path)
    attempts = read_csv(attempts_path)

    assert any(
        row["input_name"] == "FormalOscillationSeminormForGaugeLinks"
        for row in missing
    )
    assert any(
        row["input_name"] == "FormalQhpBlockingMapDefinition"
        for row in missing
    )
    assert any(
        row["lemma_name"] == "BalabanCMP98LocalOscillationBoundForQhp"
        for row in attempts
    )
    assert any(
        row["lemma_name"] == "LipschitzToSquaredOscillationForQhp"
        for row in attempts
    )
    assert any(row["lemma_name"] == "AnisotropicAssumptionA" for row in attempts)


def test_sprint81_reference_arithmetic(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["l_block"] == 2
    assert summary["reference_k"] == 9
    assert summary["spatial_link_multiplicity"] == 3
    assert summary["isotropic_link_multiplicity"] == 4
    assert math.isclose(summary["squared_sum_factor_at_k9"], 3 / 512)
    assert math.isclose(
        summary["ratio_at_k9_to_isotropic_4c_squared"], 3 / 2048
    )
    assert math.isclose(
        summary["percent_at_k9_relative_to_isotropic_4c_squared"],
        0.146484375,
    )
    assert summary["uniform_constant_form"] == "C_Q=3*C_local^2"
    assert (
        summary["qhp_per_link_bound_form"]
        == "osc_e(Q_hp)<=C_local*L^(-2k)"
    )


def test_sprint81_missing_formal_layer_fail_closed(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["route_decision"] == (
        "BALABAN_CMP98_QHP_LOCAL_OSCILLATION_MISSING_FORMAL_LAYER"
    )
    assert summary["complete"] is False
    assert summary["w1_spatial_only_blocking_available"] is True
    assert summary["sprint80_arithmetic_shell_available"] is True
    assert summary["conditional_volume_arithmetic_closes"] is True
    assert summary["formal_oscillation_seminorm_for_gauge_links"] is False
    assert summary["formal_qhp_blocking_map_definition"] is False
    assert summary["balaban_cmp98_averaging_locality_imported"] is False
    assert summary["qhp_per_link_influence_cone_l_minus_2k"] is False
    assert summary["balaban_cmp98_local_oscillation_bound_for_qhp"] is False
    assert summary["lipschitz_to_squared_oscillation_for_qhp"] is False
    assert summary["anisotropic_assumption_a"] is False
    assert summary["fixed_finite_volume_blocked_uv_closure_promoted"] is False
    assert summary["mass_gap_promoted"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint81_dependency_ordering(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "audit")

    assert summary["next_required_lemma"] == (
        "BalabanCMP98LocalOscillationBoundForQhp"
    )
    assert summary["missing_formal_inputs"] == [
        "FormalOscillationSeminormForGaugeLinks",
        "FormalQhpBlockingMapDefinition",
        "BalabanCMP98AveragingLocalityImported",
        "QhpPerLinkInfluenceConeLMinus2k",
    ]
    assert summary["next_required_lemmas"][:5] == [
        "FormalOscillationSeminormForGaugeLinks",
        "FormalQhpBlockingMapDefinition",
        "BalabanCMP98AveragingLocalityImported",
        "QhpPerLinkInfluenceConeLMinus2k",
        "BalabanCMP98LocalOscillationBoundForQhp",
    ]
