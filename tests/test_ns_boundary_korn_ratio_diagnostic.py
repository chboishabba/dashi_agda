from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_boundary_korn_ratio_diagnostic.py"


def _write_fixture(
    path: Path,
    *,
    omit_pressure: bool = False,
    true_denominator_fields: tuple[str, ...] = (),
) -> None:
    shape = (4, 4, 4)
    x = np.arange(shape[0], dtype=np.float64)[:, None, None]
    lambda2 = np.full(shape, 0.25, dtype=np.float64)
    lambda2[1:3, 1:3, 1:3] = -0.20 + 0.03 * x[1:3]
    lambda2[1, 1, 1] = 0.0
    lambda2[1, 1, 2] = 0.0
    lambda2[1, 2, 1] = 0.0

    payload = {
        "lambda2": lambda2,
        "g12": np.full(shape, 2.0, dtype=np.float64),
        "B_k": np.full(shape, 4.0, dtype=np.float64),
        "pressure_hessian_norm": np.full(shape, 1.0, dtype=np.float64),
        "beta": np.array(0.0, dtype=np.float64),
        "grid_spacing": np.array(0.5, dtype=np.float64),
    }
    for field_name in true_denominator_fields:
        payload[field_name] = np.full(
            shape,
            3.0 if field_name == "u_hessian_norm_squared" else 5.0,
            dtype=np.float64,
        )
    if omit_pressure:
        payload.pop("pressure_hessian_norm")
    np.savez(path, **payload)


def _run(path: Path, *extra: str) -> tuple[subprocess.CompletedProcess[str], dict]:
    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--component-id",
            "1",
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
            *extra,
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.stdout.strip(), completed.stdout + completed.stderr
    return completed, json.loads(completed.stdout)


def test_korn_ratio_proxy_reports_non_promoting_ratio(tmp_path: Path) -> None:
    path = tmp_path / "derived.npz"
    _write_fixture(path)

    completed, payload = _run(path)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert payload["status"] == "ok"
    assert payload["denominator_kind"] == "grad_lambda2_squared_proxy"
    assert "denominator_int_layer_true_dx" not in payload
    assert "c_empirical_true" not in payload
    assert "denominator_proxy_to_true_ratio" not in payload
    assert payload["boundary_cell_count"] > 0
    assert payload["layer_cell_count"] >= payload["boundary_cell_count"]
    assert payload["numerator_int_boundary_Bk_dH2"] > 0
    assert payload["denominator_int_layer_grad_lambda2_squared_dx"] > 0
    assert payload["c_empirical_proxy"] > 0
    assert payload["authority"]["candidate_only"] is True
    assert payload["authority"]["empirical_non_promoting"] is True
    assert payload["authority"]["theorem_authority"] is False
    assert payload["authority"]["promoted"] is False


def test_korn_ratio_missing_field_fails_closed(tmp_path: Path) -> None:
    path = tmp_path / "missing.npz"
    _write_fixture(path, omit_pressure=True)

    completed, payload = _run(path)

    assert completed.returncode != 0
    assert payload["status"] == "missing_required_field"
    assert "pressure_hessian_norm" in json.dumps(payload)


def test_korn_ratio_prefers_u_hessian_denominator_and_emits_comparison_fields(
    tmp_path: Path,
) -> None:
    path = tmp_path / "with_true_u_hessian.npz"
    _write_fixture(
        path,
        true_denominator_fields=("u_hessian_norm_squared", "velocity_hessian_norm_squared"),
    )

    completed, payload = _run(path)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert payload["status"] == "ok"
    assert payload["denominator_kind"] == "u_hessian_norm_squared"
    assert payload["denominator_int_layer_grad_lambda2_squared_dx"] > 0
    assert payload["denominator_int_layer_true_dx"] > 0
    assert payload["c_empirical_proxy"] > 0
    assert payload["c_empirical_true"] > 0
    assert payload["denominator_proxy_to_true_ratio"] > 0


def test_korn_ratio_uses_velocity_hessian_when_u_missing(tmp_path: Path) -> None:
    path = tmp_path / "with_velocity_hessian.npz"
    _write_fixture(path, true_denominator_fields=("velocity_hessian_norm_squared",))

    completed, payload = _run(path)

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert payload["status"] == "ok"
    assert payload["denominator_kind"] == "velocity_hessian_norm_squared"
    assert payload["denominator_int_layer_true_dx"] > 0
    assert payload["c_empirical_proxy"] > 0
    assert payload["c_empirical_true"] > 0
    assert payload["denominator_proxy_to_true_ratio"] > 0
    assert payload["authority"]["candidate_only"] is True
    assert payload["authority"]["empirical_non_promoting"] is True
    assert payload["authority"]["theorem_authority"] is False
    assert payload["authority"]["promoted"] is False


def test_korn_ratio_missing_component_reports_non_promoting_component_not_found(
    tmp_path: Path,
) -> None:
    path = tmp_path / "missing_component.npz"
    _write_fixture(path)

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(path),
            "--component-id",
            "99",
            "--lambda2-band",
            "1e-3",
            "--strict",
            "--json",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.stdout.strip(), completed.stdout + completed.stderr
    assert completed.returncode != 0
    payload = json.loads(completed.stdout)
    assert payload["status"] == "component_not_found"
    assert payload["authority"]["candidate_only"] is True
    assert payload["authority"]["empirical_non_promoting"] is True
