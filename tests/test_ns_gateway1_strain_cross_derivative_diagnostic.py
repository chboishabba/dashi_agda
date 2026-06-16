from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_gateway1_strain_cross_derivative_diagnostic.py"

REQUIRED_KEYS = {
    "grid_N",
    "grid_spacing",
    "domain_length",
    "result_format",
    "result_artifact_path",
    "result_artifact_format",
    "source",
    "field_metadata",
    "summary",
    "enstrophy_max_index",
    "enstrophy_max_value",
    "eigenvalues_at_max",
    "lambda2_at_max",
    "cross_derivative_e1_e2_lambda2_at_max",
    "pressure_hessian_e1_e2_at_max",
    "hess_omega2_e1_e2_at_max",
    "hess_S2_e1_e2_at_max",
    "cross_derivative_e1_e2_pressure_at_max",
    "cross_derivative_e1_e2_vorticity_norm_squared_at_max",
    "cross_derivative_e1_e2_strain_norm_squared_at_max",
    "pressure_hessian_local_decomposition_tail_e1_e2_at_max",
    "vorticity_dominance_margin",
    "vorticity_dominance_rule",
    "vorticity_dominance_condition_holds",
    "pressure_poisson_equation",
    "pressure_poisson_identity_assumption",
    "pressure_poisson_rhs_at_max",
    "pressure_poisson_rhs_mean",
    "strain_norm_squared_at_max",
    "half_vorticity_norm_squared_at_max",
    "divergence_max_abs",
    "divergence_l2_mean",
    "sign_nonpositive_at_max",
    "sign_classification",
    "sign_tolerance",
    "promotion_allowed",
    "nonlinear_riesz_sign_condition_confirmed",
    "diagnostic_scope",
}


def load_module() -> Any:
    spec = importlib.util.spec_from_file_location(
        "ns_gateway1_strain_cross_derivative_diagnostic",
        SCRIPT,
    )
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def deterministic_velocity(n: int, amplitude: float = 0.75) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    X, Y, Z = np.meshgrid(x, x, x, indexing="ij")
    u = amplitude * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -amplitude * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = 0.125 * amplitude * np.sin(Z) * np.cos(X - Y)
    return u, v, w


def require_contract(result: dict[str, Any], expected_n: int) -> None:
    json.dumps(result, sort_keys=True)
    missing = REQUIRED_KEYS.difference(result)
    assert not missing, f"missing diagnostic keys: {sorted(missing)}"

    assert result["grid_N"] == expected_n
    assert result["grid_spacing"] == 2.0 * np.pi / expected_n
    assert result["domain_length"] == 2.0 * np.pi
    assert result["result_format"] == "ns-gateway1-strain-cross-derivative-json-v1"
    assert result["result_artifact_format"] in {"json", "stdout_json"}
    if result["result_artifact_format"] == "json":
        assert isinstance(result["result_artifact_path"], str)
        assert result["result_artifact_path"]
    else:
        assert result["result_artifact_path"] is None
    assert isinstance(result["source"], str)
    assert isinstance(result["field_metadata"], dict)
    assert isinstance(result["summary"], str)
    assert "NS-GW-1 diagnostic:" in result["summary"]
    assert result["sign_classification"] in result["summary"]
    assert len(result["enstrophy_max_index"]) == 3
    assert all(isinstance(index, int) for index in result["enstrophy_max_index"])
    assert isinstance(result["enstrophy_max_value"], float)
    assert len(result["eigenvalues_at_max"]) == 3
    assert all(isinstance(value, float) for value in result["eigenvalues_at_max"])
    assert isinstance(result["lambda2_at_max"], float)
    assert isinstance(result["cross_derivative_e1_e2_lambda2_at_max"], float)
    assert isinstance(result["pressure_hessian_e1_e2_at_max"], float)
    assert isinstance(result["hess_omega2_e1_e2_at_max"], float)
    assert isinstance(result["hess_S2_e1_e2_at_max"], float)
    assert result["cross_derivative_e1_e2_pressure_at_max"] == result["pressure_hessian_e1_e2_at_max"]
    assert (
        result["cross_derivative_e1_e2_vorticity_norm_squared_at_max"]
        == result["hess_omega2_e1_e2_at_max"]
    )
    assert (
        result["cross_derivative_e1_e2_strain_norm_squared_at_max"]
        == result["hess_S2_e1_e2_at_max"]
    )
    assert isinstance(result["pressure_hessian_local_decomposition_tail_e1_e2_at_max"], float)
    assert isinstance(result["vorticity_dominance_margin"], float)
    assert isinstance(result["vorticity_dominance_rule"], str)
    assert isinstance(result["vorticity_dominance_condition_holds"], bool)
    assert result["pressure_poisson_equation"] == "-Delta p = |S|^2 - 0.5*|omega|^2"
    assert result["pressure_poisson_identity_assumption"] == "incompressible_periodic_velocity"
    assert isinstance(result["pressure_poisson_rhs_at_max"], float)
    assert isinstance(result["pressure_poisson_rhs_mean"], float)
    assert isinstance(result["strain_norm_squared_at_max"], float)
    assert isinstance(result["half_vorticity_norm_squared_at_max"], float)
    assert isinstance(result["divergence_max_abs"], float)
    assert isinstance(result["divergence_l2_mean"], float)
    assert isinstance(result["sign_nonpositive_at_max"], bool)
    assert result["sign_classification"] in {
        "positive_adverse_to_nonpositive_rule",
        "negative_supports_nonpositive_rule",
        "zero_within_tolerance",
    }
    assert isinstance(result["sign_tolerance"], float)
    assert result["promotion_allowed"] is False
    assert result["nonlinear_riesz_sign_condition_confirmed"] is False
    assert isinstance(result["diagnostic_scope"], str)
    assert result["diagnostic_scope"]


def test_run_diagnostic_importable_returns_json_serializable_contract() -> None:
    module = load_module()

    result = module.run_diagnostic(N=8, amplitude=0.5)

    require_contract(result, expected_n=8)


def test_synthetic_diagnostic_is_deterministic_for_same_inputs() -> None:
    module = load_module()

    first = module.run_diagnostic(N=12, amplitude=0.25)
    second = module.run_diagnostic(N=12, amplitude=0.25)

    require_contract(first, expected_n=12)
    require_contract(second, expected_n=12)
    assert second["enstrophy_max_index"] == first["enstrophy_max_index"]
    assert (
        second["cross_derivative_e1_e2_lambda2_at_max"]
        == first["cross_derivative_e1_e2_lambda2_at_max"]
    )


def test_npz_field_path_uses_deterministic_velocity_fixture(tmp_path: Path) -> None:
    module = load_module()
    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "velocity_fixture.npz"
    np.savez(field_path, u=u, v=v, w=w)

    result = module.run_diagnostic(N=16, amplitude=9.0, field=field_path)

    require_contract(result, expected_n=n)
    assert str(field_path) in result["source"]


def test_npz_field_metadata_is_validated_and_reported(tmp_path: Path) -> None:
    module = load_module()
    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "velocity_fixture_with_metadata.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        time=np.array(1.25, dtype=np.float64),
        snapshot_index=np.array(7, dtype=np.int64),
        source=np.array("unit-test-dns-snapshot"),
    )

    result = module.run_diagnostic(field=field_path)

    require_contract(result, expected_n=n)
    assert result["field_metadata"] == {
        "N": n,
        "domain_length": 2.0 * np.pi,
        "grid_spacing": (2.0 * np.pi) / n,
        "amplitude": 0.75,
        "time": 1.25,
        "snapshot_index": 7,
        "npz_source": "unit-test-dns-snapshot",
    }


def test_npz_field_rejects_inconsistent_domain_metadata(tmp_path: Path) -> None:
    module = load_module()
    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "bad_domain_velocity_fixture.npz"
    np.savez(field_path, u=u, v=v, w=w, N=np.array(n), domain_length=np.array(1.0))

    try:
        module.run_diagnostic(field=field_path)
    except ValueError as exc:
        assert "domain_length metadata must match" in str(exc)
    else:
        raise AssertionError("expected inconsistent domain metadata to be rejected")


def test_npz_field_rejects_inconsistent_grid_spacing_metadata(tmp_path: Path) -> None:
    module = load_module()
    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "bad_spacing_velocity_fixture.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n),
        domain_length=np.array(2.0 * np.pi),
        grid_spacing=np.array(1.0),
    )

    try:
        module.run_diagnostic(field=field_path)
    except ValueError as exc:
        assert "grid_spacing metadata must match" in str(exc)
    else:
        raise AssertionError("expected inconsistent grid spacing metadata to be rejected")


def test_cli_writes_json_output(tmp_path: Path) -> None:
    output_path = tmp_path / "diagnostic.json"

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--N",
            "8",
            "--amplitude",
            "0.5",
            "--output",
            str(output_path),
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    assert output_path.exists()
    result = json.loads(output_path.read_text(encoding="utf-8"))
    require_contract(result, expected_n=8)
    assert result["result_artifact_path"] == str(output_path)
    assert result["result_artifact_format"] == "json"
    assert completed.stdout.startswith("NS-GW-1 diagnostic:")
    assert str(output_path) in completed.stdout


def test_cli_field_fixture_path_writes_clear_artifact_summary(tmp_path: Path) -> None:
    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "fixture_style_velocity.npz"
    output_path = tmp_path / "field_diagnostic.json"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        source=np.array("fixture-style-cli-test"),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--field",
            str(field_path),
            "--output",
            str(output_path),
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    result = json.loads(output_path.read_text(encoding="utf-8"))
    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-cli-test"
    assert f"artifact={output_path}" in completed.stdout
    assert f"source=npz:{field_path}" in completed.stdout


def test_cli_help_documents_fixture_npz_contract() -> None:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    assert "scripts/ns_gateway1_fixture_npz.py" in completed.stdout
    assert "Input NPZ contract" in completed.stdout
    assert "--field" in completed.stdout
