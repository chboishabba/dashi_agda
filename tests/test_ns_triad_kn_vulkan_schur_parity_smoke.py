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
