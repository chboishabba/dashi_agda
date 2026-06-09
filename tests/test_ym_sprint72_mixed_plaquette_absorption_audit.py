from __future__ import annotations

import json
import math
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ym_sprint72_mixed_plaquette_absorption_audit.py"


pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint 72 mixed-plaquette absorption audit script is not present yet.",
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
    return read_summary(out_dir)


def read_summary(out_dir: Path) -> dict[str, Any]:
    preferred = out_dir / "ym_sprint72_mixed_plaquette_absorption_summary.json"
    candidates = [preferred, *sorted(out_dir.glob("*.json"))]
    for path in candidates:
        if not path.exists():
            continue
        payload = json.loads(path.read_text(encoding="utf-8"))
        if "route_decision" in payload:
            return payload
    raise AssertionError(f"no summary JSON with route_decision found in {out_dir}")


def assert_not_promoted(checks: dict[str, Any]) -> None:
    assert checks["clay_yang_mills_promoted"] is False


def test_default_policy_face_absorbs_mixed_plaquettes(tmp_path: Path) -> None:
    checks = run_audit(tmp_path / "default")

    assert checks["absorption_policy"] == "face"
    assert math.isclose(checks["residual_fraction"], 0.0, abs_tol=0.0)
    assert checks["mixed_plaquettes_face_absorbed"] is True
    assert checks["effective_total_leakage_times_4q"] < 1.0
    assert checks["route_decision"] == "MIXED_PLAQUETTE_ABSORPTION_CONFIRMED"
    assert_not_promoted(checks)


def test_manual_residual_fraction_point_ten_passes(tmp_path: Path) -> None:
    checks = run_audit(
        tmp_path / "manual_pass",
        "--L",
        "2",
        "--dimension",
        "4",
        "--absorption-policy",
        "manual",
        "--manual-residual-fraction",
        "0.10",
    )

    assert checks["absorption_policy"] == "manual"
    assert math.isclose(checks["residual_fraction"], 0.10)
    assert checks["effective_total_leakage_times_4q"] < 1.0
    assert checks["route_decision"] == "RESIDUAL_LEAKAGE_BELOW_10_PERCENT_CONFIRMED"
    assert_not_promoted(checks)


def test_manual_residual_fraction_point_twenty_reblocks(tmp_path: Path) -> None:
    checks = run_audit(
        tmp_path / "manual_reblock",
        "--L",
        "2",
        "--dimension",
        "4",
        "--absorption-policy",
        "manual",
        "--manual-residual-fraction",
        "0.20",
    )

    assert checks["absorption_policy"] == "manual"
    assert math.isclose(checks["residual_fraction"], 0.20)
    assert checks["effective_total_leakage_times_4q"] > 1.0
    assert checks["route_decision"] != "MIXED_PLAQUETTE_ABSORPTION_CONFIRMED"
    assert (
        "REBLOCK" in checks["route_decision"]
        or "FAIL" in checks["route_decision"]
    )
    assert_not_promoted(checks)


def test_outputs_csv_and_json_exist(tmp_path: Path) -> None:
    out_dir = tmp_path / "outputs"

    checks = run_audit(
        out_dir,
        "--L",
        "2",
        "--dimension",
        "4",
        "--absorption-policy",
        "face",
    )

    csv_outputs = sorted(out_dir.glob("*.csv"))
    json_outputs = sorted(out_dir.glob("*.json"))
    assert csv_outputs
    assert json_outputs
    assert any(
        path.name == "ym_sprint72_mixed_plaquette_absorption_summary.json"
        for path in json_outputs
    )
    assert checks["route_decision"] == "MIXED_PLAQUETTE_ABSORPTION_CONFIRMED"
    assert_not_promoted(checks)
