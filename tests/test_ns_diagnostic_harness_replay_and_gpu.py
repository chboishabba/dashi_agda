import csv
import json
import os
import subprocess
import sys
from pathlib import Path

import numpy as np
import pytest

ROOT = Path(__file__).resolve().parents[1]
HARNESS = ROOT / "scripts" / "ns_diagnostic_harness.py"
CFD_ROOT = ROOT.parent / "dashiCFD"


def _write_packet_summary(path: Path) -> None:
    fieldnames = [
        "step",
        "time",
        "K",
        "packet_count_K",
        "packet_count_Kplus1",
        "Rplus_K",
        "Rzero_K",
        "Rminus_K",
        "M_plus_plus",
        "M_plus_zero",
        "M_plus_minus",
        "s_eff_K",
        "weighted_s_eff_K",
        "rho_packet_K",
        "pass_persistence",
        "pass_source_prefix",
        "route_status",
        "promotion_status",
        "note",
    ]
    rows = [
        {
            "step": 0,
            "time": 0.0,
            "K": 1,
            "packet_count_K": 2,
            "packet_count_Kplus1": 2,
            "Rplus_K": "0.25",
            "Rzero_K": "0.50",
            "Rminus_K": "0.25",
            "M_plus_plus": "0.25",
            "M_plus_zero": "0.125",
            "M_plus_minus": "0.0625",
            "s_eff_K": "0.078125",
            "weighted_s_eff_K": "0.11048543456039805",
            "rho_packet_K": "0.50",
            "pass_persistence": 1,
            "pass_source_prefix": 1,
            "route_status": "PERSISTENCE_PASSES_REPLENISHMENT_OPEN",
            "promotion_status": "NO_PROMOTION_PACKET_LINEAGE_DIAGNOSTIC",
            "note": "fixture",
        },
        {
            "step": 0,
            "time": 0.0,
            "K": 2,
            "packet_count_K": 2,
            "packet_count_Kplus1": 2,
            "Rplus_K": "0.20",
            "Rzero_K": "0.60",
            "Rminus_K": "0.20",
            "M_plus_plus": "0.20",
            "M_plus_zero": "0.10",
            "M_plus_minus": "0.05",
            "s_eff_K": "0.07",
            "weighted_s_eff_K": "0.14",
            "rho_packet_K": "0.40",
            "pass_persistence": 1,
            "pass_source_prefix": 1,
            "route_status": "PERSISTENCE_PASSES_REPLENISHMENT_OPEN",
            "promotion_status": "NO_PROMOTION_PACKET_LINEAGE_DIAGNOSTIC",
            "note": "fixture",
        },
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def test_replay_packet_summary_writes_replenishment_outputs(tmp_path: Path) -> None:
    packet_summary = tmp_path / "ns_packet_transition_summary.csv"
    out_dir = tmp_path / "out"
    _write_packet_summary(packet_summary)

    subprocess.run(
        [
            sys.executable,
            str(HARNESS),
            "--replay-packet-summary",
            str(packet_summary),
            "--out-dir",
            str(out_dir),
            "--replenishment-decomposition-audit",
        ],
        check=True,
    )

    summary = json.loads((out_dir / "ns_replenishment_summary.json").read_text(encoding="utf-8"))
    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    assert summary["replenishment_decomposition_available"] is True
    assert summary["replenishment_decomposition_row_count"] == 2
    assert checks["diagnostic_mode"] == "sprint48_replenishment_replay_from_packet_summary"
    assert (out_dir / "ns_replenishment_decomposition.csv").exists()


def test_gpu_diagnostic_backend_smoke_if_icd_available(tmp_path: Path) -> None:
    if "VK_ICD_FILENAMES" not in os.environ:
        pytest.skip("explicit Vulkan ICD not configured")
    truth = CFD_ROOT / "outputs" / "truth3d" / "ns3d_N32_seed0_gpu_smoke.npz"
    if not truth.exists():
        pytest.skip("local GPU truth smoke artifact is not available")

    out_dir = tmp_path / "gpu"
    subprocess.run(
        [
            sys.executable,
            str(HARNESS),
            "--truth",
            str(truth),
            "--out-dir",
            str(out_dir),
            "--diagnostic-backend",
            "gpu",
            "--diagnostic-precision",
            "float64",
            "--fft-backend",
            "vkfft-vulkan",
        ],
        cwd=str(CFD_ROOT),
        check=True,
    )

    table = np.genfromtxt(out_dir / "ns_diagnostic_table.csv", delimiter=",", names=True, dtype=None, encoding=None)
    checks = json.loads((out_dir / "ns_diagnostic_checks.json").read_text(encoding="utf-8"))
    assert len(table) > 0
    assert checks["diagnostic_mode"] == "3d_vector_gpu_spectral"
    assert checks["diagnostic_precision"] == "float64"
    assert checks["gpu_runtime"]["fft_plan_backend"] == "vulkan"
    assert checks["gpu_runtime"]["complex_dtype"] == "complex128"
