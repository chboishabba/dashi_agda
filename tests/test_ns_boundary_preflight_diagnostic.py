from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace
import sys

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
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


def _write_incomplete_archive(archive_dir: Path) -> None:
    archive_dir.mkdir()
    np.savez(
        archive_dir / "boundary_slice.npz",
        lambda2=np.zeros((1, 1, 1), dtype=float),
        B_k=np.ones((1, 1, 1), dtype=float),
        time=np.array([0.0], dtype=float),
        beta=np.array([0.0], dtype=float),
    )


def test_missing_derived_arrays_fail_closed_with_status_wording(tmp_path: Path) -> None:
    archive_dir = tmp_path / "derived_archive"
    _write_incomplete_archive(archive_dir)

    args = _make_args()
    diagnostics = boundary_preflight._load_input_path(archive_dir, args)
    summary = boundary_preflight._summarize(diagnostics, args)
    rendered = boundary_preflight._render_text(summary, args)

    assert len(diagnostics) == 1
    file_diag = diagnostics[0]
    assert file_diag.status == "missing-required-keys"
    assert file_diag.missing_columns == ["g12", "pressure_hessian_norm"]
    assert file_diag.slices == []
    assert summary["status"] == "error"
    assert summary["aggregate"] == {
        "min_g12_boundary": None,
        "rho_min_boundary": None,
        "rho_mean_boundary": None,
        "rho_max_boundary": None,
        "betti0_max": None,
        "betti0_sum": None,
    }
    assert summary["missing_columns"] == ["g12", "pressure_hessian_norm"]
    assert summary["missing_files"] == []
    assert summary["errors"] == []
    assert summary["all_slices"] == []
    assert summary["contract"] == {
        "min_g12": {
            "required": ["lambda2", "g12"],
            "meaning": "boundary min(g12) on |lambda2| <= band",
        },
        "rho": {
            "required": ["lambda2", "B_k", "pressure_hessian_norm"],
            "meaning": "rho = B_k / (1 + pressure_hessian_norm) on the same boundary layer",
        },
        "betti0": {
            "required": ["lambda2", "beta or --beta-value"],
            "meaning": "Betti-0 connected-component count of {lambda2 <= beta(t)}",
        },
    }
    assert "input_contract:" in rendered
    assert "min_g12: required=lambda2, g12" in rendered
    assert "rho: required=lambda2, B_k, pressure_hessian_norm" in rendered
    assert "betti0: required=lambda2, beta or --beta-value" in rendered
    assert "status: error" in rendered
    assert "status: missing-required-keys" in rendered
    assert "missing_columns:" in rendered
    assert "  - g12" in rendered
    assert "  - pressure_hessian_norm" in rendered


def test_missing_derived_arrays_cli_exits_nonzero_with_status_wording(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    archive_dir = tmp_path / "derived_archive"
    _write_incomplete_archive(archive_dir)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "ns_boundary_preflight_diagnostic.py",
            "--input",
            str(archive_dir),
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        boundary_preflight.main()

    captured = capsys.readouterr()
    assert excinfo.value.code == 2
    assert "input_contract:" in captured.out
    assert "status: error" in captured.out
    assert "status: missing-required-keys" in captured.out
    assert "missing_columns:" in captured.out
    assert "  - g12" in captured.out
    assert "  - pressure_hessian_norm" in captured.out
