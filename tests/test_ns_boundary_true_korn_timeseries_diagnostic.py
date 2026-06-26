from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_true_korn_timeseries_diagnostic.py"


def _require_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_boundary_true_korn_timeseries_diagnostic.py is not present yet")


def _frame(seed: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    shape = (3, 3, 3)
    lambda2 = np.full(shape, 0.35 + seed, dtype=np.float64)
    lambda2[1:, 1:, 1:] = 0.0
    lambda2[1, 1, 1] = -0.02 - seed

    g12 = np.full(shape, 1.75 + seed, dtype=np.float64)
    g12[1:, 1:, 1:] = 0.5 + seed

    b_k = np.full(shape, 4.5 + seed, dtype=np.float64)
    b_k[1:, 1:, 1:] = 2.25 + seed

    pressure_hessian_norm = np.full(shape, 0.75 + seed, dtype=np.float64)
    pressure_hessian_norm[1:, 1:, 1:] = 0.25 + seed

    velocity_hessian = np.full(shape, 9.0 + seed, dtype=np.float64)
    velocity_hessian[1:, 1:, 1:] = 3.0 + seed
    return lambda2, g12, b_k, pressure_hessian_norm, velocity_hessian


def _write_timeseries(
    path: Path,
    *,
    frames: int,
    include_true_denominator: bool,
) -> None:
    series = [_frame(float(index) * 0.1) for index in range(frames)]
    payload: dict[str, Any] = {
        "lambda2": np.stack([frame[0] for frame in series]),
        "g12": np.stack([frame[1] for frame in series]),
        "B_k": np.stack([frame[2] for frame in series]),
        "pressure_hessian_norm": np.stack([frame[3] for frame in series]),
        "beta": np.array(0.0, dtype=np.float64),
        "grid_spacing": np.array(0.5, dtype=np.float64),
        "time": np.asarray([float(index) for index in range(frames)], dtype=np.float64),
    }
    if include_true_denominator:
        payload["velocity_hessian_norm_squared"] = np.stack([frame[4] for frame in series])
    np.savez(path, **payload)


def _write_raw_frame(path: Path, *, include_true_denominator: bool) -> None:
    lambda2, g12, b_k, pressure_hessian_norm, velocity_hessian = _frame(0.0)
    payload: dict[str, Any] = {
        "lambda2": lambda2,
        "g12": g12,
        "B_k": b_k,
        "pressure_hessian_norm": pressure_hessian_norm,
        "beta": np.array(0.0, dtype=np.float64),
        "grid_spacing": np.array(0.5, dtype=np.float64),
        "time": np.array(0.0, dtype=np.float64),
    }
    if include_true_denominator:
        payload["velocity_hessian_norm_squared"] = velocity_hessian
    np.savez(path, **payload)


def _run_cli(input_path: Path, output_path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(input_path),
            "--output",
            str(output_path),
            "--json",
            "--strict",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def _load_payload(completed: subprocess.CompletedProcess[str]) -> dict[str, Any]:
    assert completed.stdout.strip(), completed.stdout + completed.stderr
    return json.loads(completed.stdout)


def _assert_ok_payload(payload: dict[str, Any], *, expected_frame_count: int) -> None:
    assert payload["status"] == "ok"
    assert payload["frame_count"] == expected_frame_count
    assert len(payload["rows"]) == expected_frame_count
    assert payload["summary"]["processed_frame_count"] == expected_frame_count
    assert payload["summary"]["carrier_stable"] is True
    assert payload["authority"] == {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }
    for row in payload["rows"]:
        assert row["status"] == "ok"
        assert row["carrier_id"] is not None
        assert row["boundary_samples"] is not None
        assert row["rho_min"] is not None
        assert row["true_denominator_kind"] == "velocity_hessian_norm_squared"


def test_true_korn_timeseries_reports_ok_for_multi_frame_series(tmp_path: Path) -> None:
    _require_script()
    input_path = tmp_path / "true_korn_series.npz"
    output_path = tmp_path / "true_korn_series.json"
    _write_timeseries(input_path, frames=2, include_true_denominator=True)

    completed = _run_cli(input_path, output_path)
    payload = _load_payload(completed)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert output_path.is_file()
    assert json.loads(output_path.read_text(encoding="utf-8")) == payload
    _assert_ok_payload(payload, expected_frame_count=2)


def test_true_korn_timeseries_reports_ok_for_single_frame_per_frame_archive(
    tmp_path: Path,
) -> None:
    _require_script()
    input_path = tmp_path / "true_korn_frame.npz"
    output_path = tmp_path / "true_korn_frame.json"
    _write_raw_frame(input_path, include_true_denominator=True)

    completed = _run_cli(input_path, output_path)
    payload = _load_payload(completed)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert output_path.is_file()
    assert json.loads(output_path.read_text(encoding="utf-8")) == payload
    _assert_ok_payload(payload, expected_frame_count=1)


def test_true_korn_timeseries_missing_true_denominator_fails_closed_or_skips(
    tmp_path: Path,
) -> None:
    _require_script()
    input_path = tmp_path / "true_korn_missing_velocity_hessian.npz"
    output_path = tmp_path / "true_korn_missing_velocity_hessian.json"
    _write_timeseries(input_path, frames=2, include_true_denominator=False)

    completed = _run_cli(input_path, output_path)
    payload = _load_payload(completed)

    assert completed.returncode != 0
    assert payload["status"] in {"missing_required_field", "partial", "skipped", "skip"}
    assert "velocity_hessian_norm_squared" in json.dumps(payload, sort_keys=True)
    assert any(token in completed.stdout.lower() for token in ("missing", "skip", "closed"))


def test_true_korn_timeseries_authority_contract_is_non_promoting(tmp_path: Path) -> None:
    _require_script()
    input_path = tmp_path / "true_korn_authority.npz"
    output_path = tmp_path / "true_korn_authority.json"
    _write_timeseries(input_path, frames=2, include_true_denominator=True)

    completed = _run_cli(input_path, output_path)
    payload = _load_payload(completed)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert payload["authority"]["candidate_only"] is True
    assert payload["authority"]["empirical_non_promoting"] is True
    assert payload["authority"]["theorem_authority"] is False
    assert payload["authority"]["clay_authority"] is False
    assert payload["authority"]["runtime_authority"] is False
    assert payload["authority"]["truth_authority"] is False
    assert payload["authority"]["promoted"] is False
