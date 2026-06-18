from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_layer_thickness_diagnostic.py"


def _require_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_boundary_layer_thickness_diagnostic.py is not present yet")


def _write_fixture(path: Path, *, target_present: bool, omit_keys: tuple[str, ...] = ()) -> None:
    shape = (3, 3, 3)
    lambda2 = np.full(shape, 0.75, dtype=np.float64)
    g12 = np.full(shape, 2.0, dtype=np.float64)
    b_k_max = np.full(shape, 5.0, dtype=np.float64)
    pressure_hessian_norm = np.full(shape, 1.0, dtype=np.float64)

    if target_present:
        lambda2[0, 0, 0] = 0.10
        lambda2[0, 0, 1] = 0.20
        lambda2[0, 1, 1] = 0.30
        lambda2[2, 2, 2] = 0.15

        g12[0, 0, 0] = 0.40
        g12[0, 0, 1] = 0.25
        g12[0, 1, 1] = 0.30
        g12[2, 2, 2] = 0.80

        b_k_max[0, 0, 0] = 3.0
        b_k_max[0, 0, 1] = 3.5
        b_k_max[0, 1, 1] = 4.0
        b_k_max[2, 2, 2] = 2.0

        pressure_hessian_norm[0, 0, 0] = 0.5
        pressure_hessian_norm[0, 0, 1] = 0.4
        pressure_hessian_norm[0, 1, 1] = 0.3
        pressure_hessian_norm[2, 2, 2] = 0.6

    payload: dict[str, Any] = {
        "lambda2": lambda2,
        "g12": g12,
        "B_k_max": b_k_max,
        "pressure_hessian_norm": pressure_hessian_norm,
        "beta": np.array(0.5, dtype=np.float64),
        "grid_spacing": np.array(0.25, dtype=np.float64),
    }
    for key in omit_keys:
        payload.pop(key, None)

    np.savez(path, **payload)


def _run_cli(path: Path, *extra_args: str) -> tuple[subprocess.CompletedProcess[str], dict[str, Any]]:
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
    assert completed.stdout.strip(), completed.stdout + completed.stderr
    return completed, json.loads(completed.stdout)


def _assert_target_components(payload: dict[str, Any]) -> list[dict[str, Any]]:
    assert payload["status"] == "ok"
    assert isinstance(payload.get("target_components"), list)
    assert payload["target_components"], payload

    target_components = payload["target_components"]
    for component in target_components:
        assert isinstance(component, dict)
        assert "component_id" in component
        assert "thickness_stats" in component
        assert "gradient_stats" in component
        assert isinstance(component["thickness_stats"], dict)
        assert isinstance(component["gradient_stats"], dict)
    return target_components


def _promotion_like_values(value: Any) -> list[Any]:
    values: list[Any] = []

    def visit(node: Any) -> None:
        if isinstance(node, dict):
            for key, nested in node.items():
                lowered = str(key).lower()
                if "promot" in lowered or "diagnostic" in lowered or "metadata" in lowered:
                    values.append(nested)
                visit(nested)
        elif isinstance(node, list):
            for nested in node:
                visit(nested)

    visit(value)
    return values


def _assert_non_promoting_metadata(payload: dict[str, Any]) -> None:
    promotion_values = _promotion_like_values(payload)
    assert promotion_values, payload

    normalized: list[bool] = []
    for value in promotion_values:
        if isinstance(value, bool):
            normalized.append(value)
        elif isinstance(value, (int, np.integer)):
            normalized.append(bool(int(value)))
        elif isinstance(value, str):
            lowered = value.strip().lower()
            if lowered in {"true", "1", "yes", "promoted", "promotion", "allowed"}:
                normalized.append(True)
            elif lowered in {"false", "0", "no", "non-promoting", "not-promoting", "diagnostic", "hold"}:
                normalized.append(False)
    assert normalized, payload
    assert not any(normalized), payload


def test_boundary_layer_thickness_reports_ok_for_explicit_component_id(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "boundary_layer_component_fixture.npz"
    _write_fixture(field_path, target_present=True)

    completed, payload = _run_cli(field_path, "--component-id", "1")

    assert completed.returncode == 0, completed.stdout + completed.stderr
    target_components = _assert_target_components(payload)
    assert len(target_components) >= 1
    _assert_non_promoting_metadata(payload)


def test_boundary_layer_thickness_reports_ok_for_auto_min_g12_adjacent(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "boundary_layer_auto_fixture.npz"
    _write_fixture(field_path, target_present=True)

    completed, payload = _run_cli(field_path, "--auto-min-g12-adjacent")

    assert completed.returncode == 0, completed.stdout + completed.stderr
    target_components = _assert_target_components(payload)
    assert len(target_components) >= 1
    _assert_non_promoting_metadata(payload)


def test_boundary_layer_thickness_missing_field_fails_closed_under_strict(tmp_path: Path) -> None:
    _require_script()
    field_path = tmp_path / "boundary_layer_missing_field_fixture.npz"
    _write_fixture(field_path, target_present=True, omit_keys=("pressure_hessian_norm",))

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(field_path),
            "--json",
            "--strict",
            "--component-id",
            "1",
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


@pytest.mark.parametrize(
    ("extra_args", "fixture_kwargs", "expected_phrase"),
    [
        (("--component-id", "99"), {"target_present": True}, "component"),
        (("--auto-min-g12-adjacent",), {"target_present": False}, "target"),
    ],
)
def test_boundary_layer_thickness_component_not_found_and_no_target_fail_closed(
    tmp_path: Path,
    extra_args: tuple[str, ...],
    fixture_kwargs: dict[str, Any],
    expected_phrase: str,
) -> None:
    _require_script()
    field_path = tmp_path / ("boundary_layer_no_target_fixture.npz" if not fixture_kwargs["target_present"] else "boundary_layer_missing_component_fixture.npz")
    _write_fixture(field_path, **fixture_kwargs)

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(field_path),
            "--json",
            "--strict",
            *extra_args,
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
    assert expected_phrase in completed.stdout.lower() or expected_phrase in json.dumps(payload, sort_keys=True).lower()
