from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint103_dobrushin_wc3_audit.py"


def run_script(tmp_path: Path) -> dict:
    out_dir = tmp_path / "ym_sprint103_dobrushin_wc3"
    subprocess.run(
        ["python", str(SCRIPT), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=True,
    )
    summary = out_dir / "ym_sprint103_dobrushin_wc3_summary.json"
    return json.loads(summary.read_text())


def test_sprint103_closes_only_obligations_4_6(tmp_path: Path) -> None:
    summary = run_script(tmp_path)

    assert summary["closed_obligations"] == [
        "GaugeCovariantDobrushinComparison",
        "UniformPolymerActivityFromDobrushin",
        "WC3UniformClusterSummability",
    ]
    assert summary["gauge_covariant_dobrushin_comparison_closed_in_repo"] is True
    assert summary["uniform_polymer_activity_from_dobrushin_closed_in_repo"] is True
    assert summary["wc3_uniform_cluster_summability_closed_in_repo"] is True
    assert summary["uniform_connected_schwinger_decay_derived_in_repo"] is False
    assert summary["continuum_limit_mass_gap_derived_in_repo"] is False
    assert summary["nontrivial_4d_su3_yang_mills_measure_derived_in_repo"] is False
    assert summary["external_acceptance_token_available"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint103_records_required_arguments(tmp_path: Path) -> None:
    summary = run_script(tmp_path)
    checks = summary["agda_surface_checks"]

    assert summary["all_required_surface_checks_pass"] is True
    assert checks["explicit_cauchy_schwarz_argument"] is True
    assert checks["explicit_delta_min"] is True
    assert checks["explicit_uniform_c"] is True
    assert checks["explicit_uniform_m"] is True
    assert checks["explicit_eta4_q"] is True
    assert checks["no_empty_data_skeletons"] is True


def test_sprint103_delta_and_eta4_arithmetic(tmp_path: Path) -> None:
    summary = run_script(tmp_path)
    delta_min = 1.0 - math.exp(-4)

    assert summary["delta_min_formula"] == "1 - exp(-4)"
    assert math.isclose(summary["delta_min_numeric"], delta_min)
    assert summary["uniform_c_formula"] == "1/(1-delta_min)"
    assert math.isclose(summary["uniform_c_numeric"], 1.0 / (1.0 - delta_min))
    assert summary["uniform_m_formula"] == "delta_min/2"
    assert math.isclose(summary["uniform_m_numeric"], delta_min / 2.0)
    assert summary["blocked_l2_eta"] == 4
    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(summary["eta4_q"], 0.9271275790105094)
    assert summary["eta4_kp_arithmetic_closes"] is True
    assert summary["eta4_margin"] > 0


def test_sprint103_remaining_open_lemmas_are_exact(tmp_path: Path) -> None:
    summary = run_script(tmp_path)

    assert summary["remaining_open_lemmas"] == [
        "UniformConnectedSchwingerDecay",
        "ContinuumLimitMassGap",
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert (
        summary["route_decision"]
        == "SPRINT103_CLOSES_DOBRUSHIN_WC3_OBLIGATIONS_4_6_ONLY"
    )
