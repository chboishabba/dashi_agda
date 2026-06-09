from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint74_kp_threshold_plots.py"


pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint 74 KP threshold plotting script is not present yet.",
)


def run_audit(out_dir: Path, *args: str) -> dict[str, Any]:
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
            *args,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return json.loads((out_dir / "sprint72_kp_summary.json").read_text())


def test_threshold_constants_match_sprint72_payload(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "thresholds")

    assert math.isclose(summary["q_current"], 0.23178189475262734)
    assert math.isclose(summary["spatial_eta_q"], 0.9271275790105094)
    assert math.isclose(summary["generic_eta_q"], 1.8542551580210187)
    assert summary["spatial_weighted_kp_closes"] is True
    assert summary["generic_4d_weighted_kp_fails"] is True
    assert summary["clay_yang_mills_promoted"] is False


def test_residual_threshold_and_safe_points(tmp_path: Path) -> None:
    summary = run_audit(tmp_path / "residual")

    assert math.isclose(
        summary["residual_threshold"],
        0.107316402070709,
        rel_tol=0.0,
        abs_tol=2e-15,
    )
    assert math.isclose(summary["safe_residual_kp_ratio"], 0.994944290301034)
    assert math.isclose(summary["residual_20_kp_ratio"], 1.065154532578283)
    assert summary["ten_percent_residual_leakage_closes_kp"] is True
    assert summary["twenty_percent_residual_leakage_reblocks_kp"] is True


def test_expected_output_files_exist_and_are_nonempty(tmp_path: Path) -> None:
    out_dir = tmp_path / "outputs"
    summary = run_audit(out_dir)

    expected = [
        "sprint72_kp_constants.csv",
        "sprint72_kp_summary.json",
        "sprint72_kp_manifest.json",
        "sprint72_residual_leakage_tolerance.png",
        "sprint72_eta_threshold.png",
    ]
    for name in expected:
        path = out_dir / name
        assert path.exists(), name
        assert path.stat().st_size > 0, name
    assert (
        summary["route_decision"]
        == "KP_ARITHMETIC_CLOSED_TRANSFER_MATRIX_COMPATIBILITY_OPEN"
    )
