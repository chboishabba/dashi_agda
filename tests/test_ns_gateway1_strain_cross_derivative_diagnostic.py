from __future__ import annotations

import inspect
import importlib.util
import json
import subprocess
import sys
from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np
import pytest


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
    "derivative_operator_axis_convention",
    "divergence_max_abs",
    "divergence_l2_mean",
    "divergence_max_abs_xyz_storage",
    "divergence_l2_mean_xyz_storage",
    "divergence_max_abs_zyx_storage",
    "divergence_l2_mean_zyx_storage",
    "sign_nonpositive_at_max",
    "sign_classification",
    "sign_tolerance",
    "promotion_allowed",
    "nonlinear_riesz_sign_condition_confirmed",
    "diagnostic_scope",
    "target_mode",
    "target_selection_status",
    "target_selection_blocker",
    "target_top_enstrophy_percentile",
    "target_top_enstrophy_threshold",
    "target_top_enstrophy_mask_count",
    "target_negative_lambda2_top_mask_count",
    "target_index",
    "target_enstrophy",
    "target_strain_norm_squared",
    "target_eigenvalues",
    "target_eigenvectors",
    "target_min_local_eigenvalue_gap",
    "target_eigenframe_degenerate",
    "target_lambda2",
    "target_cross_derivative_e1_e2_lambda2",
    "target_pressure_hessian_e1_e2",
    "target_sign_classification",
    "target_sign_nonpositive",
    "target_diagnostic_status",
    "target_sign_evidence_for_promotion",
    "target_sign_evidence_blocker",
    "target_derivative_operator_axis_convention",
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


@lru_cache(maxsize=1)
def script_supports_integral_conditions_flag() -> bool:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )
    return "--integral-conditions" in completed.stdout


@lru_cache(maxsize=1)
def script_supports_kato_alignment_flag() -> bool:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )
    return "--kato-alignment" in completed.stdout


@lru_cache(maxsize=1)
def script_supports_target_flag() -> bool:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )
    return any(
        line.lstrip().startswith("--target ")
        or line.lstrip().startswith("--target,")
        or line.strip() == "--target"
        for line in completed.stdout.splitlines()
    )


@lru_cache(maxsize=1)
def script_supports_target_top_enstrophy_percentile_flag() -> bool:
    completed = subprocess.run(
        [sys.executable, str(SCRIPT), "--help"],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )
    return any(
        line.lstrip().startswith("--target-top-enstrophy-percentile")
        for line in completed.stdout.splitlines()
    )


def deterministic_velocity(n: int, amplitude: float = 0.75) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    X, Y, Z = np.meshgrid(x, x, x, indexing="ij")
    u = amplitude * np.sin(X) * np.cos(Y) * np.cos(Z)
    v = -amplitude * np.cos(X) * np.sin(Y) * np.cos(Z)
    w = 0.125 * amplitude * np.sin(Z) * np.cos(X - Y)
    return u, v, w


def deterministic_asymmetric_velocity(
    n: int,
    amplitude: float = 0.75,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    X, Y, Z = np.meshgrid(x, x, x, indexing="ij")
    base_u, base_v, base_w = deterministic_velocity(n, amplitude=amplitude)
    u = base_u + 0.04 * amplitude * np.sin(2.0 * X + 3.0 * Y)
    v = base_v + 0.03 * amplitude * np.cos(2.0 * Y + 3.0 * Z)
    w = base_w + 0.02 * amplitude * np.sin(3.0 * X + 1.0 * Z)
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
    assert_index_triplet(result["enstrophy_max_index"])
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
    assert isinstance(result["derivative_operator_axis_convention"], str)
    assert result["derivative_operator_axis_convention"]
    assert isinstance(result["divergence_max_abs"], float)
    assert isinstance(result["divergence_l2_mean"], float)
    assert np.isfinite(result["divergence_max_abs_xyz_storage"])
    assert np.isfinite(result["divergence_l2_mean_xyz_storage"])
    assert np.isfinite(result["divergence_max_abs_zyx_storage"])
    assert np.isfinite(result["divergence_l2_mean_zyx_storage"])
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

    assert result["target_mode"] in {
        "enstrophy_max",
        "lambda2_min",
        "lambda2_negative_top_enstrophy",
        "strain_max",
    }
    assert isinstance(result["target_selection_status"], str)
    assert result["target_selection_status"]
    assert result["target_selection_blocker"] is None or isinstance(
        result["target_selection_blocker"],
        str,
    )
    assert isinstance(result["target_top_enstrophy_percentile"], float)
    assert np.isfinite(result["target_top_enstrophy_percentile"])
    assert result["target_top_enstrophy_threshold"] is None or np.isfinite(
        float(result["target_top_enstrophy_threshold"]),
    )
    if result["target_top_enstrophy_mask_count"] is not None:
        assert isinstance(result["target_top_enstrophy_mask_count"], int)
        assert result["target_top_enstrophy_mask_count"] >= 0
    if result["target_negative_lambda2_top_mask_count"] is not None:
        assert isinstance(result["target_negative_lambda2_top_mask_count"], int)
        assert result["target_negative_lambda2_top_mask_count"] >= 0
    assert_index_triplet(result["target_index"])
    assert isinstance(result["target_enstrophy"], float)
    assert isinstance(result["target_strain_norm_squared"], float)
    assert len(result["target_eigenvalues"]) == 3
    assert all(isinstance(value, float) for value in result["target_eigenvalues"])
    assert len(result["target_eigenvectors"]) == 3
    assert len(result["target_eigenvectors"][0]) == 3
    assert np.all(np.isfinite(np.asarray(result["target_eigenvectors"], dtype=float)))
    assert isinstance(result["target_min_local_eigenvalue_gap"], float)
    assert isinstance(result["target_eigenframe_degenerate"], bool)
    assert isinstance(result["target_lambda2"], float)
    assert isinstance(result["target_cross_derivative_e1_e2_lambda2"], float)
    assert isinstance(result["target_pressure_hessian_e1_e2"], float)
    assert result["target_sign_classification"] in {
        "positive_adverse_to_nonpositive_rule",
        "negative_supports_nonpositive_rule",
        "zero_within_tolerance",
    }
    assert isinstance(result["target_sign_nonpositive"], bool)
    assert isinstance(result["target_diagnostic_status"], str)
    assert result["target_diagnostic_status"]
    assert isinstance(result["target_sign_evidence_for_promotion"], bool)
    assert result["target_sign_evidence_blocker"] is None or isinstance(
        result["target_sign_evidence_blocker"],
        str,
    )
    assert isinstance(result["target_derivative_operator_axis_convention"], str)
    assert result["target_derivative_operator_axis_convention"]


def assert_dict_contains(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    for key, value in expected.items():
        assert key in actual, f"missing expected key: {key}"
        assert actual[key] == value, f"unexpected value for {key}: {actual[key]!r} != {value!r}"


def count_and_validate_finite_numeric_leaves(value: Any) -> int:
    if isinstance(value, dict):
        return sum(count_and_validate_finite_numeric_leaves(item) for item in value.values())
    if isinstance(value, (list, tuple)):
        return sum(count_and_validate_finite_numeric_leaves(item) for item in value)
    if isinstance(value, np.ndarray):
        return count_and_validate_finite_numeric_leaves(value.tolist())
    if isinstance(value, bool):
        return 0
    if isinstance(value, (int, float, np.integer, np.floating)):
        assert np.isfinite(float(value)), f"non-finite numeric value: {value!r}"
        return 1
    return 0


def assert_finite_numeric_vector(value: Any, *, expected_len: int) -> None:
    assert isinstance(value, (list, tuple))
    assert len(value) == expected_len, f"unexpected vector length for value: {value!r}"
    assert count_and_validate_finite_numeric_leaves(value) == expected_len


def assert_finite_numeric_array(value: Any, *, expected_shape: tuple[int, ...]) -> None:
    array = np.asarray(value, dtype=float)
    assert array.shape == expected_shape, f"unexpected array shape for value: {value!r}"
    assert np.all(np.isfinite(array)), f"non-finite numeric values for {value!r}"


def assert_index_triplet(value: Any) -> None:
    array = np.asarray(value)
    assert array.shape == (3,), f"unexpected target index shape for value: {value!r}"
    assert all(float(item).is_integer() for item in array.tolist()), (
        f"expected integer target indices: {value!r}"
    )


def assert_kato_alignment_payload(result: dict[str, Any], *, expected_target_mode: str | None = None) -> None:
    assert result["kato_alignment_enabled"] is True
    assert result["kato_alignment_target_mode"] in {
        "enstrophy_max",
        "lambda2_min",
        "lambda2_negative_top_enstrophy",
        "strain_max",
    }
    if expected_target_mode is not None:
        assert result["kato_alignment_target_mode"] == expected_target_mode
    assert_index_triplet(result["kato_alignment_target_index"])
    assert result["kato_alignment_target_index"] == result["target_index"]
    assert_finite_numeric_vector(result["kato_alignment_directional_grad_e1_vector"], expected_len=3)
    assert_finite_numeric_vector(result["kato_alignment_directional_grad_e2_vector"], expected_len=3)
    for key in (
        "kato_alignment_e2_dot_d_e1S_e1",
        "kato_alignment_e2_dot_d_e2S_e1",
        "kato_alignment_B",
    ):
        assert isinstance(result[key], (int, float, np.integer, np.floating))
        assert np.isfinite(float(result[key])), f"non-finite numeric value for {key}: {result[key]!r}"
    assert isinstance(result["kato_alignment_B_sign"], str)
    assert len(result["kato_alignment_B_sign"]) > 0, "expected non-empty kato alignment sign string"


def assert_target_payload(result: dict[str, Any], *, expected_mode: str) -> None:
    assert result["target_mode"] == expected_mode
    assert result["target_index"] == [int(index) for index in result["target_index"]]
    assert_index_triplet(result["target_index"])
    assert isinstance(result["target_derivative_operator_axis_convention"], str)
    assert result["target_derivative_operator_axis_convention"]
    assert result["target_derivative_operator_axis_convention"] == result["derivative_operator_axis_convention"]

    if expected_mode == "lambda2_min":
        assert result["target_selection_status"] == "selected_lambda2_min"
    elif expected_mode == "lambda2_negative_top_enstrophy":
        assert result["target_selection_status"] in {
            "selected_negative_lambda2_within_top_enstrophy_mask",
            "fallback_most_negative_lambda2_in_top_enstrophy_mask",
        }
    elif expected_mode == "strain_max":
        assert result["target_selection_status"] == "selected_strain_max"
    else:
        assert result["target_selection_status"] == "selected_enstrophy_max"

    assert isinstance(result["target_top_enstrophy_threshold"], (float, type(None)))
    if expected_mode == "lambda2_negative_top_enstrophy":
        assert isinstance(result["target_top_enstrophy_threshold"], float)
        assert np.isfinite(result["target_top_enstrophy_threshold"])
        assert result["target_top_enstrophy_mask_count"] is not None
        assert result["target_negative_lambda2_top_mask_count"] is not None
        assert isinstance(result["target_top_enstrophy_mask_count"], int)
        assert isinstance(result["target_negative_lambda2_top_mask_count"], int)
        assert result["target_top_enstrophy_mask_count"] >= 0
        assert result["target_negative_lambda2_top_mask_count"] >= 0
    else:
        assert result["target_top_enstrophy_threshold"] is None
        assert result["target_top_enstrophy_mask_count"] is None
        assert result["target_negative_lambda2_top_mask_count"] is None

    assert_finite_numeric_vector(result["target_eigenvalues"], expected_len=3)
    assert_finite_numeric_array(result["target_eigenvectors"], expected_shape=(3, 3))
    assert isinstance(result["target_min_local_eigenvalue_gap"], float)
    assert np.isfinite(result["target_min_local_eigenvalue_gap"])
    assert isinstance(result["target_eigenframe_degenerate"], bool)
    assert isinstance(result["target_lambda2"], (float, int))
    assert np.isfinite(float(result["target_lambda2"]))
    assert isinstance(result["target_cross_derivative_e1_e2_lambda2"], (float, int))
    assert np.isfinite(float(result["target_cross_derivative_e1_e2_lambda2"]))
    assert isinstance(result["target_pressure_hessian_e1_e2"], (float, int))
    assert np.isfinite(float(result["target_pressure_hessian_e1_e2"]))
    assert result["target_sign_classification"] in {
        "positive_adverse_to_nonpositive_rule",
        "negative_supports_nonpositive_rule",
        "zero_within_tolerance",
    }
    assert isinstance(result["target_sign_nonpositive"], bool)
    assert isinstance(result["target_diagnostic_status"], str)
    assert result["target_diagnostic_status"]
    assert isinstance(result["target_sign_evidence_for_promotion"], bool)
    assert result["target_sign_evidence_blocker"] is None or isinstance(
        result["target_sign_evidence_blocker"], str
    )
    assert isinstance(result["target_top_enstrophy_percentile"], float)
    assert np.isfinite(result["target_top_enstrophy_percentile"])


def assert_enstrophy_max_target_payload(result: dict[str, Any]) -> None:
    assert result["target_mode"] == "enstrophy_max"
    assert result["target_index"] == result["enstrophy_max_index"]
    assert result["target_selection_status"] == "selected_enstrophy_max"
    assert result["target_top_enstrophy_threshold"] is None
    assert result["target_top_enstrophy_mask_count"] is None
    assert result["target_negative_lambda2_top_mask_count"] is None
    assert result["target_enstrophy"] == result["enstrophy_max_value"]
    assert result["target_lambda2"] == result["lambda2_at_max"]
    assert result["target_cross_derivative_e1_e2_lambda2"] == result[
        "cross_derivative_e1_e2_lambda2_at_max"
    ]
    assert result["target_pressure_hessian_e1_e2"] == result["pressure_hessian_e1_e2_at_max"]


def assert_target_payload_is_target_mode(result: dict[str, Any]) -> None:
    assert result["target_mode"] != "enstrophy_max"
    assert result["target_index"] != result["enstrophy_max_index"] or (
        result["target_selection_status"] != "selected_enstrophy_max"
    )


def parse_json_stdout(stdout: str) -> dict[str, Any]:
    start = stdout.find("{")
    end = stdout.rfind("}")
    assert start != -1 and end != -1 and end > start, "stdout did not contain JSON"
    return json.loads(stdout[start : end + 1])


def test_run_diagnostic_importable_returns_json_serializable_contract() -> None:
    module = load_module()

    result = module.run_diagnostic(N=8, amplitude=0.5)

    require_contract(result, expected_n=8)
    assert_enstrophy_max_target_payload(result)


def test_run_diagnostic_importable_supports_target_selection_when_available(
    tmp_path: Path,
) -> None:
    module = load_module()
    signature = inspect.signature(module.run_diagnostic)
    params = signature.parameters
    target_param = next((name for name in ("target", "target_mode") if name in params), None)
    if target_param is None:
        pytest.skip("run_diagnostic does not yet accept target-selection parameters")

    n = 8
    u, v, w = deterministic_asymmetric_velocity(n)
    field_path = tmp_path / "fixture_style_velocity_for_target_import.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        source=np.array("fixture-style-target-import-test"),
    )

    kwargs: dict[str, Any] = {
        "field": field_path,
        "kato_alignment": True,
    }
    if "top_enstrophy_percentile" in params:
        kwargs["top_enstrophy_percentile"] = 90.0
    kwargs[target_param] = "lambda2_min"

    result = module.run_diagnostic(**kwargs)

    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-target-import-test"
    assert_target_payload(result, expected_mode="lambda2_min")
    assert_target_payload_is_target_mode(result)
    assert_kato_alignment_payload(result, expected_target_mode="lambda2_min")


def test_run_diagnostic_target_modes_use_distinct_target_payloads_on_small_fixture(
    tmp_path: Path,
) -> None:
    if not script_supports_target_flag():
        pytest.skip("script does not expose --target yet")

    module = load_module()
    n = 8
    u, v, w = deterministic_asymmetric_velocity(n, amplitude=0.85)
    field_path = tmp_path / "target_mode_compare_fixture.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.85, dtype=np.float64),
        source=np.array("target-mode-compare-fixture"),
    )

    result_enstrophy = module.run_diagnostic(field=field_path, kato_alignment=True)
    result_lambda2 = module.run_diagnostic(
        field=field_path,
        target="lambda2_min",
        kato_alignment=True,
    )
    result_top = module.run_diagnostic(
        field=field_path,
        target="lambda2_negative_top_enstrophy",
        target_top_enstrophy_percentile=85.0,
        kato_alignment=True,
    )

    require_contract(result_enstrophy, expected_n=n)
    require_contract(result_lambda2, expected_n=n)
    require_contract(result_top, expected_n=n)

    assert result_enstrophy["target_mode"] == "enstrophy_max"
    assert_enstrophy_max_target_payload(result_enstrophy)
    assert result_lambda2["target_mode"] == "lambda2_min"
    assert result_top["target_mode"] == "lambda2_negative_top_enstrophy"
    assert result_top["target_top_enstrophy_percentile"] == 85.0
    assert_target_payload_is_target_mode(result_lambda2)
    assert_target_payload_is_target_mode(result_top)

    assert_target_payload(result_lambda2, expected_mode="lambda2_min")
    assert_target_payload(result_top, expected_mode="lambda2_negative_top_enstrophy")
    assert_kato_alignment_payload(
        result_enstrophy,
        expected_target_mode="enstrophy_max",
    )
    assert_kato_alignment_payload(
        result_lambda2,
        expected_target_mode="lambda2_min",
    )
    assert_kato_alignment_payload(
        result_top,
        expected_target_mode="lambda2_negative_top_enstrophy",
    )


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
    assert_dict_contains(result["field_metadata"], {
        "N": n,
        "domain_length": 2.0 * np.pi,
        "grid_spacing": (2.0 * np.pi) / n,
        "amplitude": 0.75,
        "time": 1.25,
        "snapshot_index": 7,
        "npz_source": "unit-test-dns-snapshot",
    })


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
    if script_supports_integral_conditions_flag():
        assert "--integral-conditions" in completed.stdout
    if script_supports_kato_alignment_flag():
        assert "--kato-alignment" in completed.stdout
    if script_supports_target_flag():
        assert "--target" in completed.stdout
    if script_supports_target_top_enstrophy_percentile_flag():
        assert "--target-top-enstrophy-percentile" in completed.stdout


def test_cli_integral_conditions_on_synthetic_fixture_have_finite_numeric_outputs(
    tmp_path: Path,
) -> None:
    if not script_supports_integral_conditions_flag():
        pytest.skip("script does not expose --integral-conditions yet")

    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "fixture_style_velocity.npz"
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
            "--integral-conditions",
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    result = parse_json_stdout(completed.stdout)
    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-cli-test"

    integral_condition_items = {
        key: value
        for key, value in result.items()
        if "integral" in key.lower() and "condition" in key.lower()
    }
    assert integral_condition_items, "expected integral-condition outputs in JSON result"

    numeric_leaf_count = sum(
        count_and_validate_finite_numeric_leaves(value)
        for value in integral_condition_items.values()
    )
    assert numeric_leaf_count > 0, "expected at least one finite numeric integral-condition output"


def test_cli_kato_alignment_on_synthetic_fixture_has_finite_numeric_outputs(
    tmp_path: Path,
) -> None:
    if not script_supports_kato_alignment_flag():
        pytest.skip("script does not expose --kato-alignment yet")

    n = 8
    u, v, w = deterministic_velocity(n)
    field_path = tmp_path / "fixture_style_velocity_for_kato_alignment.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        source=np.array("fixture-style-kato-alignment-cli-test"),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--field",
            str(field_path),
            "--kato-alignment",
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    result = parse_json_stdout(completed.stdout)
    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-kato-alignment-cli-test"
    assert_kato_alignment_payload(result)


def test_cli_target_lambda2_min_on_synthetic_fixture_has_finite_numeric_outputs(
    tmp_path: Path,
) -> None:
    if not script_supports_target_flag():
        pytest.skip("script does not expose --target yet")

    n = 8
    u, v, w = deterministic_asymmetric_velocity(n)
    field_path = tmp_path / "fixture_style_velocity_for_target_lambda2_min.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        source=np.array("fixture-style-target-lambda2-min-cli-test"),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--field",
            str(field_path),
            "--target",
            "lambda2_min",
            "--kato-alignment",
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    result = parse_json_stdout(completed.stdout)
    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-target-lambda2-min-cli-test"
    assert_target_payload(result, expected_mode="lambda2_min")
    assert result["target_top_enstrophy_percentile"] == 90.0
    assert_target_payload_is_target_mode(result)
    assert_kato_alignment_payload(result, expected_target_mode="lambda2_min")


def test_cli_target_lambda2_negative_top_enstrophy_on_synthetic_fixture_reports_selection_status(
    tmp_path: Path,
) -> None:
    if not script_supports_target_flag():
        pytest.skip("script does not expose --target yet")
    if not script_supports_target_top_enstrophy_percentile_flag():
        pytest.skip("script does not expose --target-top-enstrophy-percentile yet")

    n = 8
    u, v, w = deterministic_asymmetric_velocity(n)
    field_path = tmp_path / "fixture_style_velocity_for_target_top_enstrophy.npz"
    np.savez(
        field_path,
        u=u,
        v=v,
        w=w,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array((2.0 * np.pi) / n, dtype=np.float64),
        amplitude=np.array(0.75, dtype=np.float64),
        source=np.array("fixture-style-target-top-enstrophy-cli-test"),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--field",
            str(field_path),
            "--target",
            "lambda2_negative_top_enstrophy",
            "--target-top-enstrophy-percentile",
            "90",
            "--kato-alignment",
        ],
        check=True,
        capture_output=True,
        cwd=REPO_ROOT,
        text=True,
    )

    result = parse_json_stdout(completed.stdout)
    require_contract(result, expected_n=n)
    assert result["source"] == f"npz:{field_path}"
    assert result["field_metadata"]["npz_source"] == "fixture-style-target-top-enstrophy-cli-test"
    assert result["target_mode"] == "lambda2_negative_top_enstrophy"
    assert result["target_top_enstrophy_percentile"] == 90.0
    assert_target_payload(result, expected_mode="lambda2_negative_top_enstrophy")
    assert_target_payload_is_target_mode(result)
    assert_kato_alignment_payload(result, expected_target_mode="lambda2_negative_top_enstrophy")
