from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ns_boundary_derived_tensor_archive.py"

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import ns_boundary_preflight_diagnostic as boundary_preflight  # type: ignore[import-not-found]


def _make_args() -> SimpleNamespace:
    return SimpleNamespace(
        input=[],
        lambda2_band=boundary_preflight.DEFAULT_LAMBDA2_BAND,
        beta_value=None,
        json=False,
        strict=True,
        lenient=False,
        time_key=boundary_preflight.DEFAULT_TIME_COL,
        time_col=boundary_preflight.DEFAULT_TIME_COL,
        index_cols=boundary_preflight.DEFAULT_INDEX_COLS,
        lambda2_key=boundary_preflight.DEFAULT_LAMBDA2_KEY,
        g12_key=boundary_preflight.DEFAULT_G12_KEY,
        b_key=boundary_preflight.DEFAULT_B_KEY,
        pressure_hessian_key=boundary_preflight.DEFAULT_PRESSURE_HESSIAN_KEY,
        beta_key=boundary_preflight.DEFAULT_BETA_KEY,
        lambda2_col=boundary_preflight.DEFAULT_LAMBDA2_KEY,
        g12_col=boundary_preflight.DEFAULT_G12_KEY,
        b_col=boundary_preflight.DEFAULT_B_KEY,
        pressure_hessian_col=boundary_preflight.DEFAULT_PRESSURE_HESSIAN_KEY,
        beta_col=boundary_preflight.DEFAULT_BETA_KEY,
    )


def _require_producer_script() -> None:
    if not SCRIPT.is_file():
        pytest.skip("ns_boundary_derived_tensor_archive.py is not present yet")


def _load_module() -> Any:
    spec = importlib.util.spec_from_file_location("ns_boundary_derived_tensor_archive", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _write_taylor_green_fixture(path: Path, n: int = 8) -> None:
    grid = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False, dtype=float)
    x, y, z = np.meshgrid(grid, grid, grid, indexing="ij")

    amplitude = 1.0
    u = amplitude * np.sin(x) * np.cos(y) * np.cos(z)
    v = -amplitude * np.cos(x) * np.sin(y) * np.cos(z)
    w = 0.5 * amplitude * np.sin(z) * np.cos(x - y)
    pressure = 0.125 * (np.cos(2.0 * x) + np.cos(2.0 * y) + np.cos(2.0 * z))

    np.savez(
        path,
        u=u,
        v=v,
        w=w,
        pressure=pressure,
        N=np.array(n, dtype=np.int64),
        domain_length=np.array(2.0 * np.pi, dtype=np.float64),
        grid_spacing=np.array(2.0 * np.pi / n, dtype=np.float64),
        amplitude=np.array(amplitude, dtype=np.float64),
        time=np.array(0.0, dtype=np.float64),
        snapshot_index=np.array(0, dtype=np.int64),
        source=np.array("tests:test_ns_boundary_derived_tensor_archive:taylor_green_fixture"),
    )


def _load_npz(path: Path) -> dict[str, np.ndarray]:
    with np.load(path, allow_pickle=False) as data:
        return {name: np.asarray(data[name]) for name in data.files}


def _assert_derived_archive_contract(archive: dict[str, np.ndarray], expected_shape: tuple[int, int, int]) -> None:
    required = ("lambda2", "g12", "B_k", "pressure_hessian_norm")
    for key in required:
        assert key in archive, f"missing derived field {key!r}"
        value = np.asarray(archive[key])
        assert value.ndim == 3, f"{key} must be a 3D tensor, got shape {value.shape!r}"
        assert value.shape == expected_shape, f"{key} shape mismatch: {value.shape!r} != {expected_shape!r}"
        assert np.all(np.isfinite(value)), f"{key} contains non-finite values"

    assert "beta" in archive, "missing derived field 'beta'"
    beta = np.asarray(archive["beta"])
    assert beta.ndim in {0, 1}, f"beta should be a scalar or per-slice threshold, got shape {beta.shape!r}"
    assert np.all(np.isfinite(beta)), "beta contains non-finite values"
    assert np.all(archive["pressure_hessian_norm"] >= 0.0), "pressure_hessian_norm should be nonnegative"


def test_boundary_derived_tensor_archive_round_trips_into_preflight(tmp_path: Path) -> None:
    _require_producer_script()
    module = _load_module()
    assert callable(getattr(module, "main", None)), "producer script should expose a main() entry point"

    input_npz = tmp_path / "taylor_green_fixture.npz"
    output_npz = tmp_path / "derived_boundary_archive.npz"
    _write_taylor_green_fixture(input_npz, n=8)

    completed = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--input",
            str(input_npz),
            "--output",
            str(output_npz),
        ],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert output_npz.is_file(), "producer script did not write the derived archive"

    archive = _load_npz(output_npz)
    _assert_derived_archive_contract(archive, expected_shape=(8, 8, 8))

    args = _make_args()
    args.lambda2_band = float(np.nanmax(np.abs(archive["lambda2"]))) + np.finfo(float).eps
    args.beta_value = float(np.nanmax(archive["lambda2"]))

    diagnostics = boundary_preflight._load_input_path(output_npz, args)
    summary = boundary_preflight._summarize(diagnostics, args)
    rendered = boundary_preflight._render_text(summary, args)

    assert len(diagnostics) == 1
    file_diag = diagnostics[0]
    assert file_diag.status == "ok"
    assert file_diag.beta_source == "cli-beta-value"
    assert file_diag.missing_columns == []
    assert file_diag.missing_files == []
    assert file_diag.errors == []
    assert len(file_diag.slices) == 1

    slice_diag = file_diag.slices[0]
    assert slice_diag.boundary_cells > 0
    assert slice_diag.min_g12_boundary is not None
    assert np.isfinite(slice_diag.min_g12_boundary)
    assert slice_diag.rho_min_boundary is not None
    assert np.isfinite(slice_diag.rho_min_boundary)
    assert slice_diag.rho_mean_boundary is not None
    assert np.isfinite(slice_diag.rho_mean_boundary)
    assert slice_diag.rho_max_boundary is not None
    assert np.isfinite(slice_diag.rho_max_boundary)
    assert slice_diag.betti0 is not None
    assert slice_diag.betti0 >= 1

    assert summary["status"] == "ok"
    assert summary["missing_columns"] == []
    assert summary["missing_files"] == []
    assert summary["errors"] == []
    assert summary["all_slices"], "preflight should report at least one slice"
    assert summary["aggregate"]["betti0_max"] is not None
    assert summary["aggregate"]["betti0_sum"] is not None
    assert summary["aggregate"]["betti0_max"] >= 1
    assert summary["aggregate"]["betti0_sum"] >= 1
    assert "status: ok" in rendered
    assert "aggregate.min_g12_boundary:" in rendered
    assert "boundary_cells=" in rendered
