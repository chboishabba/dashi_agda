from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint95_wc3_uniform_in_a_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint95_wc3_uniform_in_a"
    / "ym_sprint95_wc3_uniform_in_a_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint95_closes_wc3_uniform_in_a_only() -> None:
    summary = run_script()

    assert summary["uniform_bound_for_all_a_required"] is True
    assert summary["wc3_uniform_in_a_closed_in_repo"] is True
    assert summary["uniform_connected_schwinger_decay_derived_in_repo"] is False
    assert summary["continuum_limit_mass_gap_derived_in_repo"] is False
    assert summary["clay_yang_mills_promoted"] is False


def test_sprint95_eta4_kp_arithmetic_is_the_summability_gate() -> None:
    summary = run_script()

    assert summary["blocked_l2_eta"] == 4
    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(summary["eta4_q"], 0.9271275790105094)
    assert summary["eta4_kp_arithmetic_closes"] is True
    assert summary["eta4_margin"] > 0


def test_sprint95_remaining_open_lemmas_are_exact() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "UniformConnectedSchwingerDecay",
        "ContinuumLimitMassGap",
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert summary["route_decision"] == "SPRINT95_CLOSES_WC3_UNIFORM_IN_A_ONLY"
