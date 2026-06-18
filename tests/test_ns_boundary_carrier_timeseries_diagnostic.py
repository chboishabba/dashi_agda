from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_carrier_timeseries_diagnostic.py"


def _run_subprocess(args: list[str]) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    repo_path = str(REPO_ROOT)
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = repo_path if not existing else f"{repo_path}:{existing}"
    return subprocess.run(
        args,
        cwd=REPO_ROOT,
        env=env,
        check=False,
        capture_output=True,
        text=True,
    )


def _frame(seed: float) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    shape = (4, 4, 4)
    lambda2 = np.full(shape, 0.25 + seed, dtype=np.float64)
    lambda2[1:3, 1:3, 1:3] = -0.20
    lambda2[1, 1, 1] = 0.0
    lambda2[1, 1, 2] = 0.0
    lambda2[1, 2, 1] = 0.0
    g12 = np.full(shape, 2.0 + seed, dtype=np.float64)
    g12[1, 1, 1] = 0.7 + seed
    b_k = np.full(shape, 4.0 + seed, dtype=np.float64)
    pressure = np.full(shape, 1.0, dtype=np.float64)
    pressure[1, 1, 1] = 0.5
    return lambda2, g12, b_k, pressure


def _write_derived_series(
    path: Path,
    *,
    omit_scale: bool = False,
    omit_pressure: bool = False,
    include_velocity_hessian: bool = False,
) -> None:
    frames = [_frame(0.0), _frame(0.1)]
    payload = {
        "lambda2": np.stack([frame[0] for frame in frames]),
        "g12": np.stack([frame[1] for frame in frames]),
        "B_k": np.stack([frame[2] for frame in frames]),
        "pressure_hessian_norm": np.stack([frame[3] for frame in frames]),
        "beta": np.array(0.0, dtype=np.float64),
        "grid_spacing": np.array(0.5, dtype=np.float64),
        "time": np.asarray([0.0, 1.0], dtype=np.float64),
    }
    if include_velocity_hessian:
        velocity_hessian = np.stack(
            [
                np.full_like(frame[0], 7.0 + seed, dtype=np.float64)
                for seed, frame in ((0.0, frames[0]), (0.1, frames[1]))
            ]
        )
        payload["velocity_hessian_norm_squared"] = velocity_hessian
    if omit_scale:
        payload.pop("grid_spacing")
    if omit_pressure:
        payload.pop("pressure_hessian_norm")
    np.savez(path, **payload)


def _write_raw_frame(path: Path, *, include_velocity_hessian: bool = False) -> None:
    lambda2, g12, b_k, pressure = _frame(0.0)
    payload = {
        "lambda2": lambda2,
        "g12": g12,
        "B_k": b_k,
        "pressure_hessian_norm": pressure,
        "beta": np.array(0.0, dtype=np.float64),
        "grid_spacing": np.array(0.5, dtype=np.float64),
    }
    if include_velocity_hessian:
        payload["velocity_hessian_norm_squared"] = np.full_like(lambda2, 7.0, dtype=np.float64)
    np.savez(path, **payload)


def _assert_ok_rows(payload: dict[str, object], *, expect_true_denominator_kind: str | None) -> None:
    assert payload["status"] == "ok"
    assert payload["warnings"] == []
    assert payload["errors"] == []
    for row in payload["rows"]:
        assert row["status"] == "ok"
        assert row["carrier_id"] is not None
        assert row["boundary_samples"] is not None
        assert row["rho_min"] is not None
        assert row["true_denominator_kind"] == expect_true_denominator_kind


def test_carrier_timeseries_reports_two_derived_frames(tmp_path: Path) -> None:
    path = tmp_path / "derived_series.npz"
    _write_derived_series(path)
    completed = _run_subprocess(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--output",
            str(path.with_suffix(".json")),
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
        ]
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["frame_count"] == 2
    assert len(payload["rows"]) == 2
    assert payload["summary"]["processed_frame_count"] == 2
    assert payload["summary"]["carrier_stable"] is True
    _assert_ok_rows(payload, expect_true_denominator_kind=None)


def test_carrier_timeseries_preserves_true_denominator_kind_for_derived_frames(
    tmp_path: Path,
) -> None:
    path = tmp_path / "derived_series_with_velocity_hessian.npz"
    _write_derived_series(path, include_velocity_hessian=True)
    completed = _run_subprocess(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--output",
            str(path.with_suffix(".json")),
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
        ]
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["frame_count"] == 2
    assert len(payload["rows"]) == 2
    _assert_ok_rows(payload, expect_true_denominator_kind="velocity_hessian_norm_squared")


def test_carrier_timeseries_preserves_true_denominator_kind_for_raw_frame(
    tmp_path: Path,
) -> None:
    path = tmp_path / "raw_frame_with_velocity_hessian.npz"
    _write_raw_frame(path, include_velocity_hessian=True)
    completed = _run_subprocess(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--output",
            str(path.with_suffix(".json")),
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
        ]
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode == 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["frame_count"] == 1
    assert len(payload["rows"]) == 1
    _assert_ok_rows(payload, expect_true_denominator_kind="velocity_hessian_norm_squared")


def test_carrier_timeseries_reports_partial_when_scale_metadata_is_missing(
    tmp_path: Path,
) -> None:
    path = tmp_path / "derived_series_no_scale.npz"
    _write_derived_series(path, omit_scale=True)
    completed = _run_subprocess(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--output",
            str(path.with_suffix(".json")),
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
        ]
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode != 0, completed.stdout + completed.stderr
    payload = json.loads(completed.stdout)
    assert payload["status"] == "partial"
    assert payload["warnings"]
    assert "missing_scale_metadata_using_index_units" in payload["warnings"]
    assert payload["summary"]["processed_frame_count"] == 2
    assert payload["summary"]["carrier_stable"] is True


def test_carrier_timeseries_missing_required_field_fails_closed(tmp_path: Path) -> None:
    path = tmp_path / "derived_series.npz"
    _write_derived_series(path, omit_pressure=True)
    completed = _run_subprocess(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--output",
            str(path.with_suffix(".json")),
            "--json",
        ]
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode != 0
    payload = json.loads(completed.stdout)
    assert payload["status"] == "missing_required_field"
    assert payload["errors"]
