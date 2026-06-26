from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_component_diagnostic.py"


def _require_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_boundary_component_diagnostic.py is not present yet")


def _write_fixture(path: Path, *, disconnected: bool, omit_keys: tuple[str, ...] = ()) -> None:
    shape = (3, 3, 3)
    lambda2 = np.full(shape, 0.25, dtype=np.float64)
    g12 = np.full(shape, 1.5, dtype=np.float64)
    b_k_max = np.full(shape, 4.0, dtype=np.float64)
    pressure_hessian_norm = np.full(shape, 0.5, dtype=np.float64)

    if disconnected:
        lambda2[0, 0, 0] = 0.0
        lambda2[2, 2, 2] = 0.0
        g12[0, 0, 0] = 0.1
        g12[2, 2, 2] = 0.8
        b_k_max[0, 0, 0] = 0.7
        b_k_max[2, 2, 2] = 0.05
        pressure_hessian_norm[0, 0, 0] = 0.25
        pressure_hessian_norm[2, 2, 2] = 0.75
    else:
        lambda2[0, 0, 0] = 0.0
        lambda2[0, 0, 1] = 0.0
        g12[0, 0, 0] = 0.05
        g12[0, 0, 1] = 0.2
        b_k_max[0, 0, 0] = 0.9
        b_k_max[0, 0, 1] = 0.6
        pressure_hessian_norm[0, 0, 0] = 0.1
        pressure_hessian_norm[0, 0, 1] = 0.2

    payload: dict[str, Any] = {
        "lambda2": lambda2,
        "g12": g12,
        "B_k_max": b_k_max,
        "pressure_hessian_norm": pressure_hessian_norm,
        "beta": np.array(0.12, dtype=np.float64),
        "grid_spacing": np.array(1.0, dtype=np.float64),
    }
    for key in omit_keys:
        payload.pop(key, None)

    np.savez(path, **payload)


def _run_cli(path: Path, *extra_args: str) -> dict[str, Any]:
    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--json",
            "--strict",
            *extra_args,
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    return json.loads(completed.stdout)


def _assert_same_component_contract(value: Any, *, expected: bool) -> None:
    if isinstance(value, (bool, np.bool_)):
        assert bool(value) is expected
        return

    arr = np.asarray(value)
    assert arr.dtype == np.bool_, f"same_component should be boolean, got {arr.dtype!r}"
    assert arr.shape != (), "same_component should carry component shape when not scalar"
    if expected:
        assert np.all(arr), f"expected same_component to be all true, got {arr!r}"
    else:
        assert not np.all(arr), f"expected same_component to contain a false entry, got {arr!r}"


def _assert_component_payload(component: Any) -> None:
    assert isinstance(component, dict)
    for key in ("volume_stats", "boundary_stats", "gradient_stats"):
        assert key in component, f"missing {key} in component payload"
        assert isinstance(component[key], dict), f"{key} must be a dict"


def test_component_diagnostic_reports_ok_and_same_component_true(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "component_fixture_connected.npz"
    _write_fixture(field_path, disconnected=False)

    result = _run_cli(field_path)

    assert result["status"] == "ok"
    assert "same_component" in result
    _assert_same_component_contract(result["same_component"], expected=True)

    assert "min_g12_component" in result
    assert "min_rho_component" in result
    _assert_component_payload(result["min_g12_component"])
    _assert_component_payload(result["min_rho_component"])
    assert result["min_g12_component"]["volume_stats"]
    assert result["min_g12_component"]["boundary_stats"]
    assert result["min_g12_component"]["gradient_stats"]
    assert result["min_rho_component"]["volume_stats"]
    assert result["min_rho_component"]["boundary_stats"]
    assert result["min_rho_component"]["gradient_stats"]


def test_component_diagnostic_reports_ok_and_same_component_false(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "component_fixture_disconnected.npz"
    _write_fixture(field_path, disconnected=True)

    result = _run_cli(field_path)

    assert result["status"] == "ok"
    assert "same_component" in result
    _assert_same_component_contract(result["same_component"], expected=False)
    assert "min_g12_component" in result
    assert "min_rho_component" in result
    _assert_component_payload(result["min_g12_component"])
    _assert_component_payload(result["min_rho_component"])


def test_component_diagnostic_missing_field_fails_closed_under_strict(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "component_fixture_missing_field.npz"
    _write_fixture(field_path, disconnected=False, omit_keys=("pressure_hessian_norm",))

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(field_path),
            "--json",
            "--strict",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode != 0
    assert completed.stdout.strip()
    payload = json.loads(completed.stdout)
    assert payload["status"] != "ok"
    assert "pressure_hessian_norm" in completed.stdout
    assert "pressure_hessian_norm" in json.dumps(payload, sort_keys=True)


def test_component_diagnostic_no_boundary_cells_fails_closed(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "component_fixture_no_boundary.npz"

    shape = (3, 3, 3)
    np.savez(
        field_path,
        lambda2=np.full(shape, 0.4, dtype=np.float64),
        g12=np.full(shape, 1.5, dtype=np.float64),
        B_k_max=np.full(shape, 4.0, dtype=np.float64),
        pressure_hessian_norm=np.full(shape, 0.5, dtype=np.float64),
        beta=np.array(0.12, dtype=np.float64),
        grid_spacing=np.array(1.0, dtype=np.float64),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(field_path),
            "--json",
            "--strict",
            "--lambda2-band",
            "0.05",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode != 0
    assert completed.stdout.strip()
    payload = json.loads(completed.stdout)
    assert payload["status"] != "ok"
    assert "boundary" in completed.stdout.lower()
    assert "boundary" in json.dumps(payload, sort_keys=True).lower()
