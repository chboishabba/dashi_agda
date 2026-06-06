from __future__ import annotations

import json
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint92_master_wc3_adjoint_correction_audit.py"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint92_master_wc3_adjoint_correction"
    / "ym_sprint92_master_wc3_adjoint_correction_summary.json"
)


def run_audit() -> dict:
    subprocess.run(
        ["python", str(SCRIPT), "--repo-root", str(REPO_ROOT)],
        cwd=REPO_ROOT,
        check=True,
    )
    return json.loads(SUMMARY.read_text())


def test_sprint92_corrects_su3_k10_failure_and_k11_pass() -> None:
    payload = run_audit()

    assert payload["all_gates_pass"] is True
    assert (
        payload["route_decision"]
        == "YM_SPRINT92_ADJOINT_CORRECTION_NUMERIC_BOUNDARY_OPEN"
    )
    assert payload["cases"]["su2_k9"]["status"] == "passes"
    assert payload["cases"]["su3_k9"]["status"] == "fails"
    assert payload["cases"]["su3_k10"]["status"] == "fails"
    assert payload["cases"]["su3_k11"]["status"] == "passes_arithmetically"


def test_sprint92_keeps_wc3_and_clay_fail_closed() -> None:
    payload = run_audit()

    assert payload["clay_yang_mills_promoted"] is False
    assert payload["remaining_open_lemmas"] == [
        "BalabanQhpLocalConstantBound",
        "BalabanCMP116PolymerMassBound",
        "AdjointRepresentationSharperBound-or-BlockingDepthK11PhysicalValidation",
        "WeakCouplingWindowSU3",
    ]

    gates = {row["gate_name"]: row["actual_value"] for row in payload["gates"]}
    assert gates["QhpWitnessUnexported"] is True
    assert gates["PolymerMassWitnessUnexported"] is True
    assert gates["WC3StillFalse"] is True
    assert gates["ClayStillFalse"] is True
