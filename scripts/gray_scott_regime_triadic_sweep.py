#!/usr/bin/env python3
"""
Sweep Gray-Scott triadic diagnostics over small regimes.

This runner is a diagnostic/falsification surface for the Abel/triadic/sheaf
machinery. It does not provide evidence for Navier-Stokes, Yang-Mills, or Clay
promotion.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_PRESETS = ("spots", "worms", "chaos")
QUICK_PRESETS = ("spots", "mitosis", "chaos")
REGIME_LABELS = {
    "spots": "stable_pattern",
    "worms": "stable_pattern",
    "solitons": "localized_coherent_pattern",
    "mitosis": "unstable_splitting_pattern",
    "chaos": "chaotic_or_broad_pattern",
}


@dataclass(frozen=True)
class SweepCase:
    preset: str
    seed: int
    grid: int
    steps: int


def parse_int_list(value: str) -> list[int]:
    out: list[int] = []
    for part in value.split(","):
        part = part.strip()
        if not part:
            continue
        out.append(int(part))
    if not out:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return out


def parse_str_list(value: str) -> list[str]:
    out = [part.strip() for part in value.split(",") if part.strip()]
    if not out:
        raise argparse.ArgumentTypeError("expected at least one value")
    return out


def normalized_entropy(weights: list[float]) -> float:
    total = float(sum(max(0.0, x) for x in weights))
    if total <= 0.0:
        return 0.0
    probs = [max(0.0, x) / total for x in weights if x > 0.0]
    if len(probs) <= 1:
        return 0.0
    entropy = -sum(p * math.log(p) for p in probs)
    return float(entropy / math.log(len(weights))) if len(weights) > 1 else 0.0


def run_case(
    case: SweepCase,
    *,
    harness: Path,
    analysis_frames: int,
    triads_per_frame: int,
    max_modes: int,
    shells: int,
    angle_bins: int,
    coherent_bins: int,
    timeout: float,
) -> dict[str, Any]:
    cmd = [
        sys.executable,
        str(harness),
        "--json",
        "--preset",
        case.preset,
        "--seed",
        str(case.seed),
        "--grid",
        str(case.grid),
        "--steps",
        str(case.steps),
        "--analysis-frames",
        str(analysis_frames),
        "--triads-per-frame",
        str(triads_per_frame),
        "--max-modes",
        str(max_modes),
        "--shells",
        str(shells),
        "--angle-bins",
        str(angle_bins),
        "--coherent-bins",
        str(coherent_bins),
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, check=False)
    if proc.returncode != 0:
        return {
            "case": case.__dict__,
            "ok": False,
            "returncode": proc.returncode,
            "stdout_head": proc.stdout[:1000],
            "stderr_head": proc.stderr[:1000],
            "promotion": False,
            "clay_promotion": False,
        }

    try:
        report = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return {
            "case": case.__dict__,
            "ok": False,
            "returncode": proc.returncode,
            "decode_error": str(exc),
            "stdout_head": proc.stdout[:1000],
            "stderr_head": proc.stderr[:1000],
            "promotion": False,
            "clay_promotion": False,
        }

    return summarize_case(case, report, cmd)


def summarize_case(case: SweepCase, report: dict[str, Any], cmd: list[str]) -> dict[str, Any]:
    triadic = report.get("triadic_sampling", {})
    zero_mode = triadic.get("zero_mode_proxy", {})
    abel = triadic.get("abel_late_time_measure_proxy", {})
    shell = report.get("fourier_shell_energy", {}).get("uv2", {})
    late_shell = shell.get("late_abel_weighted", [])
    accepted = int(triadic.get("triads_accepted", 0))
    candidates = int(triadic.get("triad_candidates", 0))
    leakage = float(triadic.get("leakage_proxy", 0.0))
    coherence = float(triadic.get("pattern_coherence_proxy", 0.0))
    zero_width = float(zero_mode.get("output_width", 0.0))
    all_width = float(zero_mode.get("all_output_width", 0.0))
    angular_entropy = float(abel.get("entropy_normalized", 0.0))
    abel_concentration = float(abel.get("coherent_mass_fraction", 0.0))
    shell_entropy = normalized_entropy([float(x) for x in late_shell])
    triadic_spread = float(max(0.0, min(1.0, 0.5 * leakage + 0.5 * angular_entropy)))
    accepted_fraction = float(accepted / candidates) if candidates else 0.0
    usefulness = diagnostic_usefulness(
        accepted=accepted,
        accepted_fraction=accepted_fraction,
        leakage=leakage,
        coherence=coherence,
        zero_width=zero_width,
        angular_entropy=angular_entropy,
        shell_entropy=shell_entropy,
    )

    return {
        "case": case.__dict__,
        "ok": True,
        "promotion": False,
        "clay_promotion": False,
        "regime_label": REGIME_LABELS.get(case.preset, "unclassified_gray_scott_regime"),
        "command": cmd,
        "metrics": {
            "accepted_triads": accepted,
            "triad_candidates": candidates,
            "accepted_fraction": accepted_fraction,
            "abel_concentration_proxy": abel_concentration,
            "leakage_proxy": leakage,
            "triadic_spread_proxy": triadic_spread,
            "coherence_proxy": coherence,
            "zero_mode_width": zero_width,
            "all_output_width": all_width,
            "output_support_width": all_width,
            "angular_entropy_normalized": angular_entropy,
            "uv2_shell_entropy_normalized": shell_entropy,
            "zero_mode_mass_fraction": float(zero_mode.get("weighted_mass_fraction", 0.0)),
            "direction_residual_median": float(
                triadic.get("direction_residual", {}).get("median", 0.0)
            ),
            "diagnostic_usefulness": usefulness,
        },
        "classification": classify_case(
            accepted=accepted,
            leakage=leakage,
            coherence=coherence,
            zero_width=zero_width,
            shell_entropy=shell_entropy,
            angular_entropy=angular_entropy,
        ),
    }


def diagnostic_usefulness(
    *,
    accepted: int,
    accepted_fraction: float,
    leakage: float,
    coherence: float,
    zero_width: float,
    angular_entropy: float,
    shell_entropy: float,
) -> float:
    sample_quality = min(1.0, accepted / 500.0) * min(1.0, accepted_fraction / 0.75)
    contrast = abs(leakage - (1.0 - coherence))
    nondegenerate_width = min(1.0, zero_width / 0.25)
    score = (
        0.28 * sample_quality
        + 0.22 * shell_entropy
        + 0.18 * angular_entropy
        + 0.16 * leakage
        + 0.10 * nondegenerate_width
        + 0.06 * contrast
    )
    return float(max(0.0, min(1.0, score)))


def classify_case(
    *,
    accepted: int,
    leakage: float,
    coherence: float,
    zero_width: float,
    shell_entropy: float,
    angular_entropy: float,
) -> str:
    if accepted < 100:
        return "low_sample_unreliable"
    if leakage < 0.35 and coherence > 0.45 and shell_entropy < 0.55:
        return "coherent_low_leakage_pattern_candidate"
    if leakage > 0.65 and shell_entropy > 0.55 and angular_entropy > 0.55:
        return "broad_high_leakage_pattern_candidate"
    if zero_width > 0.35 and leakage > 0.45:
        return "wide_zero_mode_proxy_leakage_candidate"
    if shell_entropy < 0.25 and angular_entropy < 0.25:
        return "spectrally_degenerate_low_information"
    return "mixed_diagnostic_candidate"


def aggregate_by_preset(case_reports: list[dict[str, Any]]) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for report in case_reports:
        if not report.get("ok"):
            continue
        grouped.setdefault(report["case"]["preset"], []).append(report)

    out: list[dict[str, Any]] = []
    for preset, rows in grouped.items():
        metrics = [row["metrics"] for row in rows]
        avg = {
            key: float(sum(float(m[key]) for m in metrics) / len(metrics))
            for key in (
                "accepted_triads",
                "abel_concentration_proxy",
                "leakage_proxy",
                "triadic_spread_proxy",
                "coherence_proxy",
                "zero_mode_width",
                "output_support_width",
                "angular_entropy_normalized",
                "uv2_shell_entropy_normalized",
                "diagnostic_usefulness",
            )
        }
        classes: dict[str, int] = {}
        for row in rows:
            classes[row["classification"]] = classes.get(row["classification"], 0) + 1
        out.append(
            {
                "preset": preset,
                "regime_label": REGIME_LABELS.get(preset, "unclassified_gray_scott_regime"),
                "runs": len(rows),
                "mean_metrics": avg,
                "classifications": classes,
                "promotion": False,
                "clay_promotion": False,
            }
        )

    out.sort(key=lambda row: row["mean_metrics"]["diagnostic_usefulness"], reverse=True)
    for rank, row in enumerate(out, start=1):
        row["diagnostic_rank"] = rank
    return out


def build_cases(presets: list[str], seeds: list[int], grids: list[int], steps: list[int]) -> list[SweepCase]:
    cases: list[SweepCase] = []
    for preset in presets:
        for seed in seeds:
            for grid in grids:
                for step_count in steps:
                    cases.append(SweepCase(preset=preset, seed=seed, grid=grid, steps=step_count))
    return cases


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Sweep Gray-Scott triadic diagnostics")
    parser.add_argument(
        "--harness",
        type=Path,
        default=Path("scripts/gray_scott_triadic_defect_harness.py"),
    )
    parser.add_argument("--presets", type=parse_str_list, default=list(DEFAULT_PRESETS))
    parser.add_argument("--seeds", type=parse_int_list, default=[20260608, 7])
    parser.add_argument("--grids", type=parse_int_list, default=[20, 24])
    parser.add_argument("--steps", type=parse_int_list, default=[60])
    parser.add_argument("--analysis-frames", type=int, default=8)
    parser.add_argument("--triads-per-frame", type=int, default=256)
    parser.add_argument("--max-modes", type=int, default=64)
    parser.add_argument("--shells", type=int, default=12)
    parser.add_argument("--angle-bins", type=int, default=24)
    parser.add_argument("--coherent-bins", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--json-output", type=Path, default=None)
    parser.add_argument(
        "--json",
        action="store_true",
        help="Accepted for manifest compatibility; this sweep always emits JSON.",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Run stable/unstable/chaotic calibration cases under the 10s policy.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.quick:
        args.presets = list(QUICK_PRESETS)
        args.seeds = [20260608]
        args.grids = [18]
        args.steps = [42]
        args.analysis_frames = min(args.analysis_frames, 5)
        args.triads_per_frame = min(args.triads_per_frame, 120)
        args.max_modes = min(args.max_modes, 40)
        args.shells = min(args.shells, 9)
        args.angle_bins = min(args.angle_bins, 18)
        args.coherent_bins = min(args.coherent_bins, 3)
        args.timeout = min(args.timeout, 3.0)

    cases = build_cases(args.presets, args.seeds, args.grids, args.steps)
    case_reports = [
        run_case(
            case,
            harness=args.harness,
            analysis_frames=args.analysis_frames,
            triads_per_frame=args.triads_per_frame,
            max_modes=args.max_modes,
            shells=args.shells,
            angle_bins=args.angle_bins,
            coherent_bins=args.coherent_bins,
            timeout=args.timeout,
        )
        for case in cases
    ]
    failures = [row for row in case_reports if not row.get("ok")]
    report = {
        "harness": "GrayScottRegimeTriadicSweep",
        "diagnostic_only": True,
        "promotion": False,
        "clay_promotion": False,
        "clay_promoted": False,
        "policy": {
            "lane": "P1 calibration only",
            "quick_mode": bool(args.quick),
            "timeout_policy_seconds": 10,
            "case_timeout_seconds": args.timeout,
            "regime_labels": REGIME_LABELS,
        },
        "notes": [
            "Gray-Scott is a diagnostic sandbox only.",
            "No incompressibility, Leray pressure, vorticity stretching, gauge quotient, or OS transfer is tested.",
        ],
        "sweep": {
            "cases": len(cases),
            "successful": len(cases) - len(failures),
            "failed": len(failures),
            "presets": args.presets,
            "seeds": args.seeds,
            "grids": args.grids,
            "steps": args.steps,
        },
        "regime_ranking": aggregate_by_preset(case_reports),
        "case_reports": case_reports,
    }

    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
