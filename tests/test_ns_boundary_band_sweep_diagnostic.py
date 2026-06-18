from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_band_sweep_diagnostic.py"


def _require_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_boundary_band_sweep_diagnostic.py is not present yet")


def _write_fixture(path: Path) -> None:
    shape = (3, 3, 3)
    lambda2 = np.full(shape, 7.5e-4, dtype=np.float64)
    component_labels = np.ones(shape, dtype=np.int64)

    component_cells = [
        (1, 1, 1, 5.0e-5),
        (1, 1, 2, 1.5e-4),
        (1, 2, 1, 3.5e-4),
        (2, 1, 1, 6.0e-4),
    ]
    for x, y, z, value in component_cells:
        component_labels[x, y, z] = 2
        lambda2[x, y, z] = value

    b_k_max = np.full(shape, 4.0, dtype=np.float64)
    g12 = np.full(shape, 1.75, dtype=np.float64)
    rho = np.full(shape, 0.25, dtype=np.float64)
    grad_lambda2_norm_squared = np.full(shape, 8.0, dtype=np.float64)
    velocity_hessian_norm_squared = np.full(shape, 12.0, dtype=np.float64)
    strain_hessian_norm_squared = np.full(shape, 3.0, dtype=np.float64)
    antisym_hessian_norm_squared = np.full(shape, 5.0, dtype=np.float64)

    for index, (x, y, z, _) in enumerate(component_cells):
        b_k_max[x, y, z] = 10.0 + index
        g12[x, y, z] = 1.10 + 0.05 * index
        rho[x, y, z] = 0.80 - 0.10 * index
        grad_lambda2_norm_squared[x, y, z] = 0.20 + 0.10 * index
        velocity_hessian_norm_squared[x, y, z] = 2.0 + 0.25 * index
        strain_hessian_norm_squared[x, y, z] = 0.40 + 0.05 * index
        antisym_hessian_norm_squared[x, y, z] = 0.60 + 0.04 * index

    np.savez(
        path,
        lambda2=lambda2,
        component_labels=component_labels,
        B_k_max=b_k_max,
        g12=g12,
        rho=rho,
        grad_lambda2_norm_squared=grad_lambda2_norm_squared,
        velocity_hessian_norm_squared=velocity_hessian_norm_squared,
        strain_hessian_norm_squared=strain_hessian_norm_squared,
        antisym_hessian_norm_squared=antisym_hessian_norm_squared,
        frame=np.array(10, dtype=np.int64),
        component_id=np.array(2, dtype=np.int64),
    )


def _run_cli(input_path: Path, output_path: Path) -> tuple[subprocess.CompletedProcess[str], dict[str, Any]]:
    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(input_path),
            "--frame",
            "10",
            "--component-id",
            "2",
            "--bands",
            "5e-4",
            "2.5e-4",
            "1e-4",
            "--json",
            "--output",
            str(output_path),
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.stdout.strip(), completed.stdout + completed.stderr
    return completed, json.loads(completed.stdout)


def _authority_contract(payload: dict[str, Any]) -> dict[str, Any]:
    authority = payload.get("authority")
    assert isinstance(authority, dict), payload
    return authority


def _band_value(row: dict[str, Any]) -> float:
    if "band" in row:
        return float(row["band"])
    if "lambda2_band" in row:
        return float(row["lambda2_band"])
    raise AssertionError(f"missing band field in row: {row}")


def test_band_sweep_reports_ok_rows_and_non_promoting_authority(tmp_path: Path) -> None:
    _require_script()

    input_path = tmp_path / "band_sweep_fixture.npz"
    output_path = tmp_path / "band_sweep_output.json"
    _write_fixture(input_path)

    completed, payload = _run_cli(input_path, output_path)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert output_path.is_file()
    assert json.loads(output_path.read_text(encoding="utf-8")) == payload

    assert payload["contract"] == "ns_boundary_band_sweep_diagnostic"
    assert payload["status"] == "ok"
    assert payload["frame"] == 10
    assert payload["component_id"] == 2
    assert payload["authority"] == {
        "candidate_only": True,
        "empirical_non_promoting": True,
        "truth_authority": False,
        "theorem_authority": False,
        "clay_authority": False,
        "runtime_authority": False,
        "promoted": False,
    }

    rows = payload["rows"]
    assert isinstance(rows, list)
    assert len(rows) == 3

    expected_bands = [5.0e-4, 2.5e-4, 1.0e-4]
    for row, expected_band in zip(rows, expected_bands, strict=True):
        assert _band_value(row) == pytest.approx(expected_band)
        assert row["boundary_cell_count"] > 0
        assert row["c_empirical_true"] > 0
        assert row["alpha_strain_sq"] >= 0
        assert row["alpha_omega_sq"] >= 0
        assert row["min_g12"] >= 0
        assert row["rho_min"] >= 0
        assert np.isfinite(row["c_empirical_true"])
        assert np.isfinite(row["alpha_strain_sq"])
        assert np.isfinite(row["alpha_omega_sq"])
        assert np.isfinite(row["min_g12"])
        assert np.isfinite(row["rho_min"])

    assert _authority_contract(payload)["promoted"] is False
