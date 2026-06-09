#!/usr/bin/env python3
"""
Gray-Scott triadic defect diagnostic harness.

This is a diagnostic/falsification sandbox for Abel/triadic/sheaf machinery.
It is not evidence for Navier-Stokes or Yang-Mills Clay promotion.

The harness either loads u/v arrays from an NPZ file or runs a small built-in
2D Gray-Scott simulator, then reports:
  * Fourier shell energy over time
  * sampled uv^2 Fourier triads
  * late-time Abel-weighted triad measure proxies
  * pattern coherence and leakage proxies
  * zero-mode output width proxy
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

try:
    import numpy as np
except ImportError as exc:  # pragma: no cover - exercised only on missing dependency.
    raise SystemExit(
        "Missing required dependency: numpy. "
        "Install numpy in the active project environment to run the Gray-Scott "
        "triadic calibration harness."
    ) from exc


PRESETS: dict[str, dict[str, float]] = {
    "spots": {"du": 0.16, "dv": 0.08, "f": 0.060, "k": 0.062, "dt": 1.0},
    "worms": {"du": 0.16, "dv": 0.08, "f": 0.035, "k": 0.060, "dt": 1.0},
    "mitosis": {"du": 0.16, "dv": 0.08, "f": 0.0367, "k": 0.0649, "dt": 1.0},
    "solitons": {"du": 0.16, "dv": 0.08, "f": 0.030, "k": 0.062, "dt": 1.0},
    "chaos": {"du": 0.16, "dv": 0.08, "f": 0.026, "k": 0.051, "dt": 1.0},
}


@dataclass(frozen=True)
class GrayScottParams:
    grid: int
    steps: int
    seed: int
    preset: str
    du: float
    dv: float
    f: float
    k: float
    dt: float


def laplacian_periodic(x: np.ndarray) -> np.ndarray:
    return (
        np.roll(x, 1, axis=0)
        + np.roll(x, -1, axis=0)
        + np.roll(x, 1, axis=1)
        + np.roll(x, -1, axis=1)
        - 4.0 * x
    )


def simulate_gray_scott(params: GrayScottParams) -> tuple[np.ndarray, np.ndarray]:
    rng = np.random.default_rng(params.seed)
    grid = params.grid
    u = np.ones((grid, grid), dtype=np.float64)
    v = np.zeros((grid, grid), dtype=np.float64)

    radius = max(2, grid // 8)
    center = grid // 2
    u[center - radius : center + radius, center - radius : center + radius] = 0.50
    v[center - radius : center + radius, center - radius : center + radius] = 0.25
    u += 0.02 * rng.standard_normal((grid, grid))
    v += 0.02 * rng.standard_normal((grid, grid))

    u_series = np.empty((params.steps, grid, grid), dtype=np.float64)
    v_series = np.empty_like(u_series)
    for t in range(params.steps):
        uvv = u * v * v
        u = u + (params.du * laplacian_periodic(u) - uvv + params.f * (1.0 - u)) * params.dt
        v = v + (params.dv * laplacian_periodic(v) + uvv - (params.f + params.k) * v) * params.dt
        u = np.clip(u, -1.0, 2.0)
        v = np.clip(v, -1.0, 2.0)
        u_series[t] = u
        v_series[t] = v
    return u_series, v_series


def load_uv_npz(path: Path) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    with np.load(path, allow_pickle=False) as data:
        keys = set(data.files)
        for u_key, v_key in (("u", "v"), ("U", "V"), ("u_series", "v_series")):
            if u_key in keys and v_key in keys:
                return normalize_uv_arrays(data[u_key], data[v_key]), {
                    "path": str(path),
                    "keys": sorted(data.files),
                    "format": f"{u_key}/{v_key}",
                }

        for key in ("fields", "uv", "state", "states", "frames"):
            if key not in keys:
                continue
            arr = np.asarray(data[key])
            if arr.ndim == 4 and arr.shape[1] == 2:
                return normalize_uv_arrays(arr[:, 0], arr[:, 1]), {
                    "path": str(path),
                    "keys": sorted(data.files),
                    "format": f"{key}[T,2,H,W]",
                }
            if arr.ndim == 4 and arr.shape[-1] == 2:
                return normalize_uv_arrays(arr[..., 0], arr[..., 1]), {
                    "path": str(path),
                    "keys": sorted(data.files),
                    "format": f"{key}[T,H,W,2]",
                }

        raise ValueError(
            f"Could not find u/v arrays in {path}. Expected keys u/v, U/V, "
            "u_series/v_series, or fields/uv/state/states/frames with a 2-channel axis."
        )


def normalize_uv_arrays(u: np.ndarray, v: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    u_arr = np.asarray(u, dtype=np.float64)
    v_arr = np.asarray(v, dtype=np.float64)
    if u_arr.shape != v_arr.shape:
        raise ValueError(f"u and v shapes differ: {u_arr.shape} vs {v_arr.shape}")
    if u_arr.ndim == 2:
        u_arr = u_arr[None, ...]
        v_arr = v_arr[None, ...]
    if u_arr.ndim != 3:
        raise ValueError(f"u/v arrays must be [T,H,W] or [H,W], got {u_arr.shape}")
    if u_arr.shape[1] != u_arr.shape[2]:
        raise ValueError(f"only square grids are supported, got {u_arr.shape[1:]}")
    return u_arr, v_arr


def fftfreq_int(grid: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    freqs = np.fft.fftfreq(grid) * grid
    kx, ky = np.meshgrid(freqs.astype(int), freqs.astype(int), indexing="ij")
    radius = np.sqrt(kx.astype(float) ** 2 + ky.astype(float) ** 2)
    return kx, ky, radius


def shell_energy(series: np.ndarray, shell_count: int) -> dict[str, Any]:
    grid = series.shape[1]
    _, _, radius = fftfreq_int(grid)
    shell_idx = np.minimum(radius.astype(int), shell_count - 1)
    out = np.zeros((series.shape[0], shell_count), dtype=np.float64)
    for t, frame in enumerate(series):
        power = np.abs(np.fft.fft2(frame)) ** 2 / float(grid * grid)
        out[t] = np.bincount(shell_idx.ravel(), weights=power.ravel(), minlength=shell_count)
    late = late_weights(series.shape[0], tau=max(2.0, series.shape[0] / 5.0))
    return {
        "shell_count": shell_count,
        "initial": out[0].tolist(),
        "final": out[-1].tolist(),
        "late_abel_weighted": (late @ out).tolist(),
        "total_initial": float(out[0].sum()),
        "total_final": float(out[-1].sum()),
        "total_late_abel_weighted": float((late @ out).sum()),
    }


def late_weights(n: int, tau: float) -> np.ndarray:
    idx = np.arange(n, dtype=np.float64)
    raw = np.exp(-(n - 1 - idx) / max(tau, 1e-9))
    return raw / raw.sum()


def top_modes(field_hat: np.ndarray, max_modes: int, min_radius: float = 1.0) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    grid = field_hat.shape[0]
    kx, ky, radius = fftfreq_int(grid)
    amp = np.abs(field_hat).ravel()
    mask = radius.ravel() >= min_radius
    valid = np.flatnonzero(mask)
    if len(valid) == 0:
        return np.zeros((0, 2), dtype=int), np.zeros(0), np.zeros(0, dtype=complex)
    take = min(max_modes, len(valid))
    best_rel = np.argpartition(amp[valid], -take)[-take:]
    flat = valid[best_rel]
    order = np.argsort(amp[flat])[::-1]
    flat = flat[order]
    coords = np.stack([kx.ravel()[flat], ky.ravel()[flat]], axis=1).astype(int)
    weights = amp[flat].astype(np.float64)
    coeffs = field_hat.ravel()[flat]
    return coords, weights, coeffs


def wrap_k(k: np.ndarray, grid: int) -> np.ndarray:
    return ((k + grid // 2) % grid) - grid // 2


def direction_2d(k: np.ndarray) -> np.ndarray:
    norm = float(np.linalg.norm(k))
    if norm <= 0:
        return np.array([0.0, 0.0])
    return k.astype(np.float64) / norm


def angular_bins(directions: np.ndarray, weights: np.ndarray, bins: int) -> tuple[np.ndarray, np.ndarray]:
    if len(directions) == 0:
        return np.zeros(bins), np.linspace(0.0, math.pi, bins + 1)
    angles = np.mod(np.arctan2(directions[:, 1], directions[:, 0]), math.pi)
    hist, edges = np.histogram(angles, bins=bins, range=(0.0, math.pi), weights=weights)
    return hist.astype(np.float64), edges


def resultant_coherence(directions: np.ndarray, weights: np.ndarray) -> float:
    if len(directions) == 0 or float(np.sum(weights)) <= 0:
        return 0.0
    angles = np.arctan2(directions[:, 1], directions[:, 0])
    z = np.sum(weights * np.exp(2j * angles)) / np.sum(weights)
    return float(np.abs(z))


def output_width_proxy(directions: np.ndarray, normals: int = 720) -> float:
    if len(directions) == 0:
        return 0.0
    theta = np.linspace(0.0, math.pi, normals, endpoint=False)
    n = np.stack([np.cos(theta), np.sin(theta)], axis=1)
    dots = np.abs(n @ directions.T)
    return float(np.max(np.min(dots, axis=1)))


def triadic_sample_diagnostics(
    u_series: np.ndarray,
    v_series: np.ndarray,
    *,
    rng: np.random.Generator,
    frames: int,
    triads_per_frame: int,
    max_modes: int,
    angle_bins: int,
    coherent_bins: int,
) -> dict[str, Any]:
    n = u_series.shape[0]
    grid = u_series.shape[1]
    frame_idx = np.unique(np.linspace(max(0, n // 3), n - 1, min(frames, n), dtype=int))
    time_w = late_weights(len(frame_idx), tau=max(1.0, len(frame_idx) / 3.0))

    all_dirs: list[np.ndarray] = []
    all_weights: list[float] = []
    all_residuals: list[float] = []
    frame_reports: list[dict[str, Any]] = []
    total_candidates = 0
    rejected_zero_output = 0

    for local_t, t in enumerate(frame_idx):
        u_hat = np.fft.fft2(u_series[t])
        v_hat = np.fft.fft2(v_series[t])
        u_modes, u_w, u_c = top_modes(u_hat, max_modes=max_modes)
        v_modes, v_w, v_c = top_modes(v_hat, max_modes=max_modes)
        if len(u_modes) == 0 or len(v_modes) == 0:
            continue

        u_prob = u_w / max(float(u_w.sum()), 1e-12)
        v_prob = v_w / max(float(v_w.sum()), 1e-12)
        accepted = 0
        frame_weight = 0.0
        frame_dirs: list[np.ndarray] = []
        frame_weights: list[float] = []

        for _ in range(triads_per_frame):
            iu = int(rng.choice(len(u_modes), p=u_prob))
            iv1 = int(rng.choice(len(v_modes), p=v_prob))
            iv2 = int(rng.choice(len(v_modes), p=v_prob))
            kout = wrap_k(u_modes[iu] + v_modes[iv1] + v_modes[iv2], grid)
            total_candidates += 1
            if int(kout[0]) == 0 and int(kout[1]) == 0:
                rejected_zero_output += 1
                continue
            raw_weight = abs(u_c[iu] * v_c[iv1] * v_c[iv2])
            weight = float(raw_weight) * float(time_w[local_t])
            if weight <= 0:
                continue
            d = direction_2d(kout)
            residual = direction_residual(u_modes[iu], v_modes[iv1], v_modes[iv2], kout)
            all_dirs.append(d)
            all_weights.append(weight)
            all_residuals.append(residual)
            frame_dirs.append(d)
            frame_weights.append(weight)
            frame_weight += weight
            accepted += 1

        frame_reports.append(
            {
                "t": int(t),
                "accepted_triads": int(accepted),
                "weighted_mass": float(frame_weight),
                "coherence": resultant_coherence(np.asarray(frame_dirs), np.asarray(frame_weights))
                if frame_dirs
                else 0.0,
            }
        )

    directions = np.asarray(all_dirs, dtype=np.float64)
    weights = np.asarray(all_weights, dtype=np.float64)
    residuals = np.asarray(all_residuals, dtype=np.float64)
    hist, edges = angular_bins(directions, weights, angle_bins)
    mass = float(weights.sum())
    probs = hist / mass if mass > 0 else hist
    entropy = float(-np.sum(probs[probs > 0] * np.log(probs[probs > 0])))
    entropy_norm = entropy / math.log(angle_bins) if angle_bins > 1 else 0.0
    top_idx = np.argsort(hist)[::-1][: max(1, coherent_bins)]
    coherent_mass = float(hist[top_idx].sum())
    coherence = resultant_coherence(directions, weights)
    leakage_proxy = float(max(0.0, 1.0 - coherent_mass / mass)) if mass > 0 else 0.0

    zero_mask = np.zeros(len(directions), dtype=bool)
    if len(directions) > 0 and mass > 0:
        angles = np.mod(np.arctan2(directions[:, 1], directions[:, 0]), math.pi)
        bin_idx = np.clip(np.digitize(angles, edges) - 1, 0, angle_bins - 1)
        residual_cut = float(np.quantile(residuals, 0.35)) if len(residuals) else 0.0
        zero_mask = np.isin(bin_idx, top_idx) & (residuals <= residual_cut)

    zero_dirs = directions[zero_mask]
    zero_weights = weights[zero_mask]
    top_bins = [
        {
            "bin": int(i),
            "angle_center": float(0.5 * (edges[i] + edges[i + 1])),
            "mass": float(hist[i]),
        }
        for i in top_idx
    ]

    return {
        "frames_used": [int(x) for x in frame_idx],
        "triad_candidates": int(total_candidates),
        "triads_accepted": int(len(directions)),
        "rejected_zero_output": int(rejected_zero_output),
        "weighted_mass": mass,
        "angle_bins": int(angle_bins),
        "coherent_bins": int(coherent_bins),
        "top_output_bins": top_bins,
        "abel_late_time_measure_proxy": {
            "angular_histogram": hist.tolist(),
            "angular_edges": edges.tolist(),
            "entropy": entropy,
            "entropy_normalized": float(entropy_norm),
            "coherent_mass_fraction": float(coherent_mass / mass) if mass > 0 else 0.0,
        },
        "pattern_coherence_proxy": coherence,
        "leakage_proxy": leakage_proxy,
        "direction_residual": {
            "mean": float(np.mean(residuals)) if len(residuals) else 0.0,
            "median": float(np.median(residuals)) if len(residuals) else 0.0,
            "p95": float(np.quantile(residuals, 0.95)) if len(residuals) else 0.0,
        },
        "zero_mode_proxy": {
            "triads": int(np.count_nonzero(zero_mask)),
            "weighted_mass": float(zero_weights.sum()) if len(zero_weights) else 0.0,
            "weighted_mass_fraction": float(zero_weights.sum() / mass) if mass > 0 else 0.0,
            "output_width": output_width_proxy(zero_dirs),
            "all_output_width": output_width_proxy(directions),
        },
        "frame_reports": frame_reports,
    }


def direction_residual(ku: np.ndarray, kv1: np.ndarray, kv2: np.ndarray, kout: np.ndarray) -> float:
    inputs = [direction_2d(ku), direction_2d(kv1), direction_2d(kv2)]
    out = direction_2d(kout)
    if float(np.linalg.norm(out)) <= 0:
        return 1.0
    alignments = [abs(float(np.dot(out, x))) for x in inputs if float(np.linalg.norm(x)) > 0]
    if not alignments:
        return 1.0
    return float(1.0 - max(alignments))


def summarize_fields(u: np.ndarray, v: np.ndarray) -> dict[str, Any]:
    uvv = u * v * v
    return {
        "shape": list(u.shape),
        "u_mean_initial": float(np.mean(u[0])),
        "u_mean_final": float(np.mean(u[-1])),
        "v_mean_initial": float(np.mean(v[0])),
        "v_mean_final": float(np.mean(v[-1])),
        "uv2_mean_initial": float(np.mean(uvv[0])),
        "uv2_mean_final": float(np.mean(uvv[-1])),
        "u_variance_final": float(np.var(u[-1])),
        "v_variance_final": float(np.var(v[-1])),
    }


def discover_sibling_evidence() -> dict[str, Any]:
    candidates = [
        "../dashifine/newtest/grayscott_krr.py",
        "../dashitest/dashifine/newtest/grayscott_krr.py",
        "../dashitest/docs/grayscott_quotient.md",
        "../dashitest/outputs/grayscott_krr_run1/run_summary.txt",
        "../dashitest/outputs/grayscott_krr/run_20260106_112335/run_summary.txt",
    ]
    present = [p for p in candidates if Path(p).exists()]
    return {
        "read_only_scan": True,
        "present_gray_scott_artifacts": present,
        "notes": [
            "Sibling Gray-Scott KRR scripts define gray_scott_step and simulate_gray_scott.",
            "Sibling outputs expose summaries/plots/CSV, but no u/v trajectory NPZ was discovered in the shallow Gray-Scott output scan.",
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Gray-Scott triadic defect diagnostic harness")
    parser.add_argument("--input-npz", type=Path, default=None, help="Optional NPZ with u/v arrays.")
    parser.add_argument("--json-output", type=Path, default=None, help="Optional JSON output path.")
    parser.add_argument(
        "--json",
        action="store_true",
        help="Accepted for manifest compatibility; this harness always emits JSON.",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Use a capped smoke configuration suitable for timeout 10s runs.",
    )
    parser.add_argument("--grid", type=int, default=32)
    parser.add_argument("--steps", type=int, default=160)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--preset", choices=sorted(PRESETS), default="spots")
    parser.add_argument("--du", type=float, default=None)
    parser.add_argument("--dv", type=float, default=None)
    parser.add_argument("--f", type=float, default=None)
    parser.add_argument("--k", type=float, default=None)
    parser.add_argument("--dt", type=float, default=None)
    parser.add_argument("--analysis-frames", type=int, default=16)
    parser.add_argument("--triads-per-frame", type=int, default=512)
    parser.add_argument("--max-modes", type=int, default=96)
    parser.add_argument("--shells", type=int, default=16)
    parser.add_argument("--angle-bins", type=int, default=36)
    parser.add_argument("--coherent-bins", type=int, default=3)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.quick:
        args.grid = min(args.grid, 20)
        args.steps = min(args.steps, 48)
        args.analysis_frames = min(args.analysis_frames, 6)
        args.triads_per_frame = min(args.triads_per_frame, 160)
        args.max_modes = min(args.max_modes, 48)
        args.shells = min(args.shells, 10)
        args.angle_bins = min(args.angle_bins, 18)
        args.coherent_bins = min(args.coherent_bins, 3)

    rng = np.random.default_rng(args.seed)
    preset = dict(PRESETS[args.preset])
    for key in ("du", "dv", "f", "k", "dt"):
        override = getattr(args, key)
        if override is not None:
            preset[key] = float(override)

    source: dict[str, Any]
    if args.input_npz is not None:
        (u_series, v_series), source = load_uv_npz(args.input_npz)
        params = None
    else:
        params = GrayScottParams(
            grid=args.grid,
            steps=args.steps,
            seed=args.seed,
            preset=args.preset,
            du=preset["du"],
            dv=preset["dv"],
            f=preset["f"],
            k=preset["k"],
            dt=preset["dt"],
        )
        u_series, v_series = simulate_gray_scott(params)
        source = {"format": "built_in_simulator", "path": None}

    shell_count = max(2, min(args.shells, u_series.shape[1] // 2 + 1))
    uv2_series = u_series * v_series * v_series
    report = {
        "harness": "GrayScottTriadicDefectHarness",
        "promotion": False,
        "clay_promotion": False,
        "clay_promoted": False,
        "diagnostic_only": True,
        "policy": {
            "lane": "P1 calibration only",
            "quick_mode": bool(args.quick),
            "timeout_policy_seconds": 10,
            "not_tested": [
                "Navier-Stokes Leray pressure",
                "vorticity stretching",
                "Lei-Ren-Tian angular condition",
                "Yang-Mills gauge quotient",
                "Clay authority",
            ],
        },
        "source": source,
        "sibling_evidence": discover_sibling_evidence(),
        "params": params.__dict__ if params is not None else {"seed": args.seed, "preset": args.preset},
        "field_summary": summarize_fields(u_series, v_series),
        "fourier_shell_energy": {
            "u": shell_energy(u_series, shell_count),
            "v": shell_energy(v_series, shell_count),
            "uv2": shell_energy(uv2_series, shell_count),
        },
        "triadic_sampling": triadic_sample_diagnostics(
            u_series,
            v_series,
            rng=rng,
            frames=args.analysis_frames,
            triads_per_frame=args.triads_per_frame,
            max_modes=args.max_modes,
            angle_bins=args.angle_bins,
            coherent_bins=args.coherent_bins,
        ),
    }

    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
