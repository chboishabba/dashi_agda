#!/usr/bin/env python3
"""Sprint 74 YM KP threshold constants and plots.

This companion diagnostic packages the arithmetic now exposed by the corrected
Sprint 70-73 transfer-matrix bookkeeping.  It does not prove Balaban transfer
matrix compatibility, all-diameter KP, a lattice mass gap, continuum transfer,
or Clay/YM promotion.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from pathlib import Path
from typing import Any


os.environ.setdefault("MPLCONFIGDIR", "/tmp/matplotlib-dashi-agda")

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


Q_CURRENT = 0.23178189475262734
ETA_SPATIAL = 4.0
ETA_GENERIC_4D = 8.0
DEFAULT_MIXED_CORRECTION_PER_FACE = 0.3592814371257485
SAFE_RESIDUAL_FRACTION = 0.10
PROMOTION_STATUS = "NO_PROMOTION_SPRINT74_KP_THRESHOLD_DIAGNOSTIC"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--q-current", type=float, default=Q_CURRENT)
    parser.add_argument("--eta-spatial", type=float, default=ETA_SPATIAL)
    parser.add_argument("--eta-generic", type=float, default=ETA_GENERIC_4D)
    parser.add_argument(
        "--mixed-correction-per-face",
        type=float,
        default=DEFAULT_MIXED_CORRECTION_PER_FACE,
    )
    parser.add_argument(
        "--safe-residual-fraction",
        type=float,
        default=SAFE_RESIDUAL_FRACTION,
    )
    return parser.parse_args()


def residual_kp_ratio(q: float, eta: float, c: float, residual_fraction: float) -> float:
    return ((1.0 + residual_fraction * c) ** 2) * eta * q


def constants(args: argparse.Namespace) -> dict[str, Any]:
    spatial_eta_q = args.eta_spatial * args.q_current
    generic_eta_q = args.eta_generic * args.q_current
    eta_threshold = 1.0 / args.q_current
    residual_threshold = (
        (math.sqrt(1.0 / spatial_eta_q) - 1.0)
        / args.mixed_correction_per_face
    )
    safe_residual_kp_ratio = residual_kp_ratio(
        args.q_current,
        args.eta_spatial,
        args.mixed_correction_per_face,
        args.safe_residual_fraction,
    )
    residual_20_kp_ratio = residual_kp_ratio(
        args.q_current,
        args.eta_spatial,
        args.mixed_correction_per_face,
        0.20,
    )
    return {
        "contract": "ym_sprint74_kp_threshold_plots",
        "promotion_status": PROMOTION_STATUS,
        "q_current": args.q_current,
        "eta_spatial": args.eta_spatial,
        "eta_generic_4d": args.eta_generic,
        "spatial_eta_q": spatial_eta_q,
        "generic_eta_q": generic_eta_q,
        "spatial_weighted_kp_closes": spatial_eta_q < 1.0,
        "generic_4d_weighted_kp_fails": generic_eta_q > 1.0,
        "eta_threshold": eta_threshold,
        "mixed_correction_per_face": args.mixed_correction_per_face,
        "residual_threshold": residual_threshold,
        "safe_residual_fraction": args.safe_residual_fraction,
        "safe_residual_kp_ratio": safe_residual_kp_ratio,
        "residual_20_fraction": 0.20,
        "residual_20_kp_ratio": residual_20_kp_ratio,
        "ten_percent_residual_leakage_closes_kp": safe_residual_kp_ratio < 1.0,
        "twenty_percent_residual_leakage_reblocks_kp": residual_20_kp_ratio > 1.0,
        "bookkeeping_lambda": 1.0,
        "bookkeeping_lambda_times_four_q": spatial_eta_q,
        "balaban_transfer_matrix_compatibility_proved": False,
        "all_diameter_weighted_kp_proved": False,
        "lattice_mass_gap_proved": False,
        "continuum_mass_gap_proved": False,
        "clay_yang_mills_promoted": False,
        "route_decision": "KP_ARITHMETIC_CLOSED_TRANSFER_MATRIX_COMPATIBILITY_OPEN",
    }


def write_constants_csv(path: Path, payload: dict[str, Any]) -> None:
    rows = [
        {
            "name": key,
            "value": value,
        }
        for key, value in payload.items()
        if isinstance(value, (bool, int, float, str))
    ]
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=["name", "value"])
        writer.writeheader()
        writer.writerows(rows)


def plot_residual_tolerance(path: Path, payload: dict[str, Any]) -> None:
    q = float(payload["q_current"])
    eta = float(payload["eta_spatial"])
    c = float(payload["mixed_correction_per_face"])
    xs = [i / 1000.0 for i in range(0, 251)]
    ys = [residual_kp_ratio(q, eta, c, x) for x in xs]

    fig, ax = plt.subplots(figsize=(8, 5), dpi=140)
    ax.plot(xs, ys, color="#1f6f8b", linewidth=2.0, label="(1 + rc)^2 * 4q")
    ax.axhline(1.0, color="#b3261e", linewidth=1.4, linestyle="--", label="KP limit")
    ax.axvline(
        float(payload["safe_residual_fraction"]),
        color="#2f7d32",
        linewidth=1.2,
        linestyle=":",
        label="safe r = 0.10",
    )
    ax.axvline(
        float(payload["residual_threshold"]),
        color="#7b1fa2",
        linewidth=1.2,
        linestyle="-.",
        label="threshold r",
    )
    ax.set_title("Sprint 74 Residual Leakage Tolerance")
    ax.set_xlabel("residual fraction r")
    ax.set_ylabel("effective KP ratio")
    ax.set_xlim(0.0, 0.25)
    ax.set_ylim(0.9, 1.12)
    ax.grid(True, alpha=0.25)
    ax.legend(loc="upper left")
    fig.tight_layout()
    fig.savefig(path)
    plt.close(fig)


def plot_entropy_threshold(path: Path, payload: dict[str, Any]) -> None:
    q = float(payload["q_current"])
    xs = [i / 20.0 for i in range(20, 201)]
    ys = [eta * q for eta in xs]

    fig, ax = plt.subplots(figsize=(8, 5), dpi=140)
    ax.plot(xs, ys, color="#0b57d0", linewidth=2.0, label="eta * q")
    ax.axhline(1.0, color="#b3261e", linewidth=1.4, linestyle="--", label="KP limit")
    ax.axvline(
        float(payload["eta_spatial"]),
        color="#2f7d32",
        linewidth=1.2,
        linestyle=":",
        label="spatial eta = 4",
    )
    ax.axvline(
        float(payload["eta_generic_4d"]),
        color="#c26401",
        linewidth=1.2,
        linestyle="-.",
        label="generic eta = 8",
    )
    ax.axvline(
        float(payload["eta_threshold"]),
        color="#7b1fa2",
        linewidth=1.2,
        linestyle="-",
        label="eta threshold",
    )
    ax.set_title("Sprint 74 Entropy Threshold")
    ax.set_xlabel("entropy factor eta")
    ax.set_ylabel("KP ratio eta * q")
    ax.set_xlim(1.0, 10.0)
    ax.set_ylim(0.0, 2.2)
    ax.grid(True, alpha=0.25)
    ax.legend(loc="upper left")
    fig.tight_layout()
    fig.savefig(path)
    plt.close(fig)


def main() -> int:
    args = parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    payload = constants(args)

    constants_csv = args.out_dir / "sprint72_kp_constants.csv"
    summary_json = args.out_dir / "sprint72_kp_summary.json"
    residual_plot = args.out_dir / "sprint72_residual_leakage_tolerance.png"
    entropy_plot = args.out_dir / "sprint72_eta_threshold.png"

    write_constants_csv(constants_csv, payload)
    summary_json.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    plot_residual_tolerance(residual_plot, payload)
    plot_entropy_threshold(entropy_plot, payload)

    manifest = {
        "contract": payload["contract"],
        "promotion_status": PROMOTION_STATUS,
        "outputs": {
            "constants_csv": constants_csv.name,
            "summary_json": summary_json.name,
            "residual_leakage_tolerance_png": residual_plot.name,
            "eta_threshold_png": entropy_plot.name,
        },
        "route_decision": payload["route_decision"],
        "clay_yang_mills_promoted": False,
    }
    (args.out_dir / "sprint72_kp_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
