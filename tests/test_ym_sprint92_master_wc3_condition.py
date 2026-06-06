from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint92_master_wc3_condition.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint92_master_wc3"
    / "ym_sprint92_master_wc3_summary.json"
)
ROWS = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint92_master_wc3"
    / "ym_sprint92_master_wc3_rows.json"
)


def run_script() -> tuple[dict, list[dict]]:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text()), json.loads(ROWS.read_text())


def test_master_wc3_condition_numerics_match_sprint92_boundary() -> None:
    summary, _ = run_script()

    assert summary["eta4_passes"] is True
    assert summary["eta6_fails"] is True
    assert summary["eta8_fails"] is True
    assert summary["su2_first_safe_k"] == 9
    assert summary["su3_first_safe_k"] == 11
    assert (
        summary["route_decision"]
        == "MASTER_WC3_SU3_CONSERVATIVE_CLOSES_ARITHMETICALLY_AT_K11"
    )
    assert (
        summary["continuum_wall"]
        == "CONTINUUM_LIMIT_MASS_GAP_NOT_KP_SPECTRAL_CONTINUITY"
    )
    assert summary["clay_yang_mills_promoted"] is False


def test_master_wc3_condition_rows_pin_su3_k10_failure_and_k11_pass() -> None:
    _, rows = run_script()
    by_case = {(row["group"], row["k"]): row for row in rows}

    assert by_case[("SU2", 9)]["passes_exp_minus_4"] is True
    assert by_case[("SU3_conservative", 10)]["passes_exp_minus_4"] is False
    assert by_case[("SU3_conservative", 11)]["passes_exp_minus_4"] is True
    assert by_case[("SU3_conservative", 10)]["margin_m0_minus_4"] < 0
    assert by_case[("SU3_conservative", 11)]["margin_m0_minus_4"] > 0


def test_master_wc3_condition_records_remaining_open_lemmas() -> None:
    summary, _ = run_script()

    assert summary["remaining_open_lemmas"] == [
        "BalabanCMP98AveragingKernelIsProbability",
        "BalabanCMP116PolymerMassBound",
        "ContractionDeltaLowerBound",
        "UniformBoundForAllA",
        "WC3UniformInA",
        "UniformConnectedSchwingerDecay",
        "ContinuumLimitMassGap",
    ]


def test_master_wc3_condition_records_typed_proof_obligations() -> None:
    summary, _ = run_script()

    obligations = {
        row["type"]: row
        for row in summary["typed_proof_obligations"]
    }
    assert obligations["ContractionDeltaLowerBound"]["sprint"] == "93"
    assert obligations["UniformBoundForAllA"]["sprint"] == "94"
    assert obligations["WC3UniformInA"]["sprint"] == "95"
    assert obligations["ContinuumLimitMassGap"]["sprint"] == "95-96"
    assert all(not row["derived_in_repo"] for row in obligations.values())
