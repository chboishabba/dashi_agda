from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
for candidate in (REPO_ROOT, REPO_ROOT / "scripts"):
    candidate_str = str(candidate)
    if candidate_str not in sys.path:
        sys.path.insert(0, candidate_str)

from scripts.ns_triad_kn_cross_shell_schur_symbolic_audit import _write_schur_checkpoint
from scripts.ns_triad_kn_cross_shell_schur_symbolic_audit import (
    _audit_row_from_checkpoint,
    _q_helical_coupling_certificate_diagnostics,
)


SCRIPT = REPO_ROOT / "scripts" / "ns_triad_kn_vulkan_schur_parity_smoke.py"


def test_vulkan_schur_parity_smoke_runs_on_synthetic_checkpoint(tmp_path: Path) -> None:
    base = tmp_path / "smoke_checkpoint"
    M_CC = np.asarray(
        [
            [2.0, -1.0, 0.0],
            [-1.0, 2.0, -1.0],
            [0.0, -1.0, 2.0],
        ],
        dtype=np.float64,
    )
    correction = np.zeros_like(M_CC)
    c_shell_levels = np.asarray([1.0, 2.0, 2.0], dtype=np.float64)
    c_mode_keys = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    _write_schur_checkpoint(
        base_path=base,
        n=3,
        cutoff=2,
        M_CC=M_CC,
        correction=correction,
        c_shell_levels=c_shell_levels,
        c_mode_keys=c_mode_keys,
        result={},
    )

    out_json = tmp_path / "smoke.json"
    subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--checkpoint",
            str(base),
            "--backend",
            "vulkan-scout",
            "--gpu-checks",
            "1",
            "--output-json",
            str(out_json),
            "--pretty",
        ],
        check=True,
    )

    payload = json.loads(out_json.read_text(encoding="utf-8"))
    assert payload["status"] == "ok"
    assert payload["restricted_sector"]["gpu_kn_authority"] is False
    assert payload["helical_certificate"]["gpuKnAuthority"] is False
    assert payload["helical_certificate"]["status"] == "ok"
    assert "gpuBackendStatus" in payload["helical_certificate"]
    assert "relative_bound_kappa" in payload["helical_certificate"]
    assert SCRIPT.read_text(encoding="utf-8").find("--backend") >= 0
    assert SCRIPT.read_text(encoding="utf-8").find("vulkan-scout") >= 0


def test_helical_certificate_matrix_free_matches_dense_on_synthetic_shell() -> None:
    M_CC = np.asarray(
        [
            [2.0, -1.0, 0.0],
            [-1.0, 2.0, -1.0],
            [0.0, -1.0, 2.0],
        ],
        dtype=np.float64,
    )
    correction = np.zeros_like(M_CC)
    mode_keys = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]

    dense = _q_helical_coupling_certificate_diagnostics(
        M_CC=M_CC,
        correction=correction,
        mode_keys=mode_keys,
        max_dense_dim=8,
        q_helical_certificate_mode="dense",
    )
    matrix_free = _q_helical_coupling_certificate_diagnostics(
        M_CC=M_CC,
        correction=correction,
        mode_keys=mode_keys,
        max_dense_dim=1,
        q_helical_certificate_mode="matrix-free",
        q_helical_tol=1.0e-10,
        q_helical_maxiter=80,
    )

    assert dense["status"] == "ok"
    assert dense["evaluation_method"] == "dense"
    assert matrix_free["status"] == "ok"
    assert matrix_free["evaluation_method"] == "matrix-free"
    assert abs(dense["D_lambda_min_one_perp"] - matrix_free["D_lambda_min_one_perp"]) < 1.0e-8
    assert abs(dense["Q_lambda_min_one_perp"] - matrix_free["Q_lambda_min_one_perp"]) < 1.0e-8
    assert abs(dense["relative_bound_kappa"] - matrix_free["relative_bound_kappa"]) < 1.0e-8


def test_checkpoint_overlay_auto_switches_to_matrix_free(tmp_path: Path) -> None:
    base = tmp_path / "switch_checkpoint"
    M_CC = np.asarray(
        [
            [2.0, -1.0, 0.0],
            [-1.0, 2.0, -1.0],
            [0.0, -1.0, 2.0],
        ],
        dtype=np.float64,
    )
    correction = np.zeros_like(M_CC)
    _write_schur_checkpoint(
        base_path=base,
        n=3,
        cutoff=2,
        M_CC=M_CC,
        correction=correction,
        c_shell_levels=np.asarray([1.0, 2.0, 2.0], dtype=np.float64),
        c_mode_keys=[(1, 0, 0), (0, 1, 0), (0, 0, 1)],
        result={},
    )

    row = _audit_row_from_checkpoint(
        checkpoint_path=base,
        audit_q_helical_coupling_certificate=True,
        helical_coupling_max_dense_dim=1,
        q_helical_certificate_mode="auto",
        q_helical_tol=1.0e-10,
        q_helical_maxiter=80,
    )
    diag = row["Q_helical_coupling_certificate_diagnostics"]
    assert diag["status"] == "ok"
    assert diag["evaluation_method"] == "matrix-free"
    assert diag["qHelicalCouplingMatrixFreeRequired"] is True


def test_checkpoint_overlay_fails_closed_for_unreadable_matrices(tmp_path: Path) -> None:
    base = tmp_path / "broken_checkpoint"
    M_CC = np.asarray(
        [
            [2.0, -1.0, 0.0],
            [-1.0, 2.0, -1.0],
            [0.0, -1.0, 2.0],
        ],
        dtype=np.float64,
    )
    correction = np.zeros_like(M_CC)
    _write_schur_checkpoint(
        base_path=base,
        n=3,
        cutoff=2,
        M_CC=M_CC,
        correction=correction,
        c_shell_levels=np.asarray([1.0, 2.0, 2.0], dtype=np.float64),
        c_mode_keys=[(1, 0, 0), (0, 1, 0), (0, 0, 1)],
        result={},
    )
    matrices_path = base.with_suffix(".matrices.npz")
    matrices_path.write_text("not a zip archive", encoding="utf-8")

    row = _audit_row_from_checkpoint(checkpoint_path=base)
    assert row["verdict"] == "checkpoint_unreadable"
    assert row["checkpoint_integrity"]["status"] == "checkpoint_unreadable"
