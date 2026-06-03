#!/usr/bin/env python3
"""NS diagnostic harness for the DASHI residue bridge.

This is an evidence-only bridge falsifier.  It consumes a truth NPZ with
``omega_snapshots`` and ``steps`` and writes:

* ``ns_diagnostic_table.csv`` with one row per shell/time sample
* ``ns_diagnostic_checks.json`` with pass/fail summaries
* ``ns_diagnostic_manifest.json`` with input and governance metadata

The trusted sibling ``../dashiCFD`` truth artifacts are currently 2D scalar
vorticity traces.  For those traces the 3D vortex-stretching bridge is not
available; the harness records a fail-closed 2D-embedded diagnostic where
physical stretching is identically zero.  If supplied with 3D vector vorticity
snapshots shaped ``(T,N,N,N,3)``, it computes the spectral shell quantities
directly on the periodic box.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import time as time_module
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import numpy as np


EPS = 1e-30


@dataclass(frozen=True)
class HarnessRow:
    K: int
    t: float
    omega_l2_sq: float
    D_K: float
    T_K: float
    Q_K: float
    Rminus_K: float
    Rzero_K: float
    Rplus_K: float
    netResidue_K: float
    BeltramiDefect_K: float
    DirectionCoherenceDefect_K: float
    PressureDecorrelationScore_K: float
    AlignedConcentration_K: float
    M_plus_minus: float
    M_plus_zero: float
    M_plus_plus: float
    s_K: float
    s_eff_K: float
    weighted_s_eff_K: float
    C_K: float
    gamma_K: float
    eta_K: float
    p: int
    beta_K: float
    theta: float
    budget_K: float
    rho_K: float
    passBudget: int
    diagnostic_mode: str


@dataclass(frozen=True)
class BridgeBudgetRow:
    step: int
    time: float
    K: int
    shell_enstrophy: float
    tail_enstrophy: float
    D_K: float
    theta_NS_K: str
    Q_K_proxy: str
    R_plus_K_proxy: str
    aligned_concentration_K: str
    beta_hat_K: str
    gamma_hat_K: str
    eta_hat_K: str
    budget_hat_K: str
    adjusted_bridge_ratio: str
    promotion_status: str
    field_status: str
    unavailable_reason: str
    diagnostic_mode: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--truth", type=Path, default=None, help="truth NPZ containing omega_snapshots and steps")
    parser.add_argument(
        "--ev5-dir",
        type=Path,
        default=None,
        help="optional dashiCFD EV5 output directory; resolves manifest source_truth and imports K* metadata",
    )
    parser.add_argument("--out-dir", type=Path, required=True, help="output directory")
    parser.add_argument("--smoke", action="store_true", help="run deterministic 3D smoke data instead of --truth")
    parser.add_argument("--smoke-n", type=int, default=16, help="3D smoke grid size")
    parser.add_argument("--smoke-samples", type=int, default=3, help="3D smoke sample count")
    parser.add_argument(
        "--shell-convention",
        choices=["auto", "dyadic", "integer-radius"],
        default="auto",
        help="spectral shell projection convention; auto preserves EV5 dyadic shells and uses integer-radius for make_truth_3d artifacts",
    )
    parser.add_argument("--dt", type=float, default=None, help="override timestep")
    parser.add_argument("--nu", type=float, default=None, help="override viscosity")
    parser.add_argument("--theta", type=float, default=1.0, help="concentration penalty exponent")
    parser.add_argument("--p", type=int, default=3, help="prime lane used in budget_K")
    parser.add_argument("--coherence-threshold", type=float, default=0.65)
    parser.add_argument("--beltrami-threshold", type=float, default=0.15)
    parser.add_argument("--pressure-decorrelation-threshold", type=float, default=0.70)
    parser.add_argument("--eps", type=float, default=1e-12, help="diagnostic denominator epsilon")
    parser.add_argument(
        "--progress-every",
        type=int,
        default=0,
        help="print runtime progress every N shell rows while generating diagnostics; 0 disables progress",
    )
    return parser.parse_args()


def _load_meta(data: np.lib.npyio.NpzFile, dt_override: float | None) -> dict[str, Any]:
    meta: dict[str, Any] = {}
    if "meta_json" in data.files:
        raw = data["meta_json"]
        try:
            meta = json.loads(str(raw.item() if hasattr(raw, "item") else raw))
        except Exception:
            meta = {"meta_json_parse_error": True}
    if dt_override is not None:
        meta["dt"] = float(dt_override)
    meta.setdefault("dt", 1.0)
    return meta


def _effective_nu(meta: dict[str, Any], nu_override: float | None) -> float:
    if nu_override is not None:
        return float(nu_override)
    for key in ("nu0", "nu", "viscosity"):
        if key in meta and meta[key] is not None:
            return float(meta[key])
    return 1.0


def _synthetic_3d(samples: int, n: int, dt: float | None, nu: float | None) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    samples = max(1, int(samples))
    n = max(8, int(n))
    x = np.linspace(0.0, 2.0 * np.pi, n, endpoint=False)
    z, y, xg = np.meshgrid(x, x, x, indexing="ij")
    frames = []
    for s in range(samples):
        amp = math.exp(-0.08 * s)
        omega = np.empty((n, n, n, 3), dtype=np.float64)
        omega[..., 0] = amp * (np.sin(y) + 0.25 * np.cos(z + 0.2 * s))
        omega[..., 1] = amp * (np.sin(z) + 0.25 * np.cos(xg - 0.1 * s))
        omega[..., 2] = amp * (np.sin(xg) + 0.25 * np.cos(y + 0.3 * s))
        frames.append(omega)
    meta = {"source": "synthetic 3D smoke trace", "dt": 1.0 if dt is None else float(dt), "nu0": 0.01 if nu is None else float(nu)}
    return np.stack(frames, axis=0), np.arange(samples, dtype=np.int64), meta


def _load_truth(args: argparse.Namespace) -> tuple[np.ndarray, np.ndarray | None, np.ndarray, dict[str, Any], str]:
    if args.smoke:
        omega, steps, meta = _synthetic_3d(args.smoke_samples, args.smoke_n, args.dt, args.nu)
        return omega, None, steps, meta, "synthetic_3d_smoke"
    if args.ev5_dir is not None and args.truth is None:
        args.truth = _resolve_ev5_truth(args.ev5_dir)
    if args.truth is None:
        raise SystemExit("--truth is required unless --smoke is supplied")
    data = np.load(args.truth)
    if "omega_snapshots" not in data.files:
        raise SystemExit(f"{args.truth} lacks required key omega_snapshots")
    omega = np.asarray(data["omega_snapshots"], dtype=np.float64)
    velocity = None
    if "velocity_snapshots" in data.files:
        velocity = np.asarray(data["velocity_snapshots"], dtype=np.float64)
        if velocity.shape != omega.shape:
            raise SystemExit(
                f"{args.truth} velocity_snapshots shape {velocity.shape} does not match omega_snapshots shape {omega.shape}"
            )
    steps = np.asarray(data["steps"], dtype=np.int64) if "steps" in data.files else np.arange(omega.shape[0], dtype=np.int64)
    meta = _load_meta(data, args.dt)
    if args.ev5_dir is not None:
        ev5_meta = _load_ev5_manifest(args.ev5_dir)
        meta["ev5_dir"] = str(args.ev5_dir)
        if ev5_meta:
            meta["ev5_manifest"] = ev5_meta
            if args.nu is None and "nu" in ev5_meta:
                meta.setdefault("nu0", float(ev5_meta["nu"]))
            if args.dt is None and "dt" in ev5_meta:
                meta["dt"] = float(ev5_meta["dt"])
    return omega, velocity, steps, meta, str(args.truth)


def _load_ev5_manifest(ev5_dir: Path) -> dict[str, Any]:
    path = ev5_dir / "manifest.json"
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {"manifest_parse_error": True, "path": str(path)}


def _resolve_ev5_truth(ev5_dir: Path) -> Path:
    manifest = _load_ev5_manifest(ev5_dir)
    raw = manifest.get("source_truth")
    if not raw:
        raise SystemExit(f"{ev5_dir} lacks manifest source_truth; provide --truth explicitly")
    source = Path(str(raw))
    candidates = []
    if source.is_absolute():
        candidates.append(source)
    else:
        candidates.append(ev5_dir / source)
        for parent in ev5_dir.resolve().parents:
            candidates.append(parent / source)
    for candidate in candidates:
        if candidate.exists():
            return candidate
    raise SystemExit(f"could not resolve source_truth {raw!r} from {ev5_dir}")


def _frequencies(shape: tuple[int, ...]) -> tuple[np.ndarray, ...]:
    axes = [np.fft.fftfreq(n) * n for n in shape]
    return tuple(np.meshgrid(*axes, indexing="ij"))


def _dyadic_shells(shape: tuple[int, ...]) -> np.ndarray:
    grids = _frequencies(shape)
    radius_sq = np.zeros(shape, dtype=np.float64)
    for grid in grids:
        radius_sq += grid * grid
    radius = np.sqrt(radius_sq)
    shells = np.zeros(shape, dtype=np.int64)
    mask = radius >= 1.0
    shells[mask] = np.floor(np.log2(radius[mask])).astype(np.int64)
    return shells


def _integer_radius_shells(shape: tuple[int, ...]) -> np.ndarray:
    grids = _frequencies(shape)
    radius_sq = np.zeros(shape, dtype=np.float64)
    for grid in grids:
        radius_sq += grid * grid
    radius = np.sqrt(radius_sq)
    return np.floor(radius + 1e-12).astype(np.int64)


def _resolve_shell_convention(meta: dict[str, Any], args: argparse.Namespace, *, ndim: int) -> str:
    if args.shell_convention != "auto":
        return str(args.shell_convention)
    if ndim == 2:
        return "dyadic"
    if meta.get("source") == "synthetic 3D smoke trace":
        return "dyadic"
    if int(meta.get("dimension", 0) or 0) == 3 and (
        "k_star" in meta or meta.get("field") == "omega" or meta.get("projection") == "leray"
    ):
        return "integer-radius"
    return "dyadic"


def _shells_for_shape(shape: tuple[int, ...], meta: dict[str, Any], args: argparse.Namespace) -> tuple[np.ndarray, str]:
    convention = _resolve_shell_convention(meta, args, ndim=len(shape))
    if convention == "integer-radius":
        return _integer_radius_shells(shape), convention
    return _dyadic_shells(shape), convention


def _shell_filter_scalar(field: np.ndarray, shell_mask: np.ndarray) -> np.ndarray:
    hat = np.fft.fftn(field)
    return np.fft.ifftn(np.where(shell_mask, hat, 0.0)).real


def _shell_filter_vector(field: np.ndarray, shell_mask: np.ndarray) -> np.ndarray:
    return np.stack([_shell_filter_scalar(field[..., i], shell_mask) for i in range(field.shape[-1])], axis=-1)


def _l2_sq(field: np.ndarray) -> float:
    return float(np.mean(np.sum(field * field, axis=-1)))


def _curl_inverse_velocity(omega: np.ndarray) -> np.ndarray:
    shape = omega.shape[:-1]
    grids = _frequencies(shape)
    omega_hat = np.stack([np.fft.fftn(omega[..., i]) for i in range(3)], axis=-1)
    k = np.stack(grids, axis=-1).astype(np.float64)
    k2 = np.sum(k * k, axis=-1)
    k2_safe = np.where(k2 > 0.0, k2, 1.0)
    cross = np.cross(k, omega_hat)
    u_hat = 1j * cross / k2_safe[..., None]
    u_hat[k2 == 0.0] = 0.0
    return np.stack([np.fft.ifftn(u_hat[..., i]).real for i in range(3)], axis=-1)


def _grad_scalar(field: np.ndarray) -> list[np.ndarray]:
    shape = field.shape
    grids = _frequencies(shape)
    hat = np.fft.fftn(field)
    return [np.fft.ifftn(1j * grids[i] * hat).real for i in range(len(shape))]


def _strain_tensor(u: np.ndarray) -> np.ndarray:
    grads = [_grad_scalar(u[..., i]) for i in range(3)]
    shape = u.shape[:-1]
    strain = np.zeros(shape + (3, 3), dtype=np.float64)
    for i in range(3):
        for j in range(3):
            strain[..., i, j] = 0.5 * (grads[j][i] + grads[i][j])
    return strain


def _pressure_laplacian(u: np.ndarray) -> np.ndarray:
    grads = [_grad_scalar(u[..., i]) for i in range(3)]
    rhs = np.zeros(u.shape[:-1], dtype=np.float64)
    for i in range(3):
        for j in range(3):
            rhs -= grads[j][i] * grads[i][j]
    return rhs


def _coherence_defect(vectors: np.ndarray) -> float:
    mag = np.linalg.norm(vectors, axis=-1)
    active = mag > EPS
    if int(active.sum()) < 2:
        return 1.0
    dirs = vectors[active] / mag[active, None]
    cov = dirs.T @ dirs / float(dirs.shape[0])
    vals = np.linalg.eigvalsh(cov)
    coherence = float(vals[-1] / max(vals.sum(), EPS))
    return float(max(0.0, min(1.0, 1.0 - coherence)))


def _beltrami_defect(u: np.ndarray, omega: np.ndarray) -> float:
    u_norm = float(np.sqrt(np.mean(np.sum(u * u, axis=-1))))
    o_norm = float(np.sqrt(np.mean(np.sum(omega * omega, axis=-1))))
    if u_norm <= EPS or o_norm <= EPS:
        return 0.0
    cross_norm = float(np.sqrt(np.mean(np.sum(np.cross(u, omega) ** 2, axis=-1))))
    return float(max(0.0, min(1.0, cross_norm / (u_norm * o_norm + EPS))))


def _decorrelation_score(a: np.ndarray, h: np.ndarray) -> float:
    af = a.reshape(-1)
    hf = h.reshape(-1)
    af = af - float(af.mean())
    hf = hf - float(hf.mean())
    denom = float(np.linalg.norm(af) * np.linalg.norm(hf))
    if denom <= EPS:
        return 1.0
    corr = abs(float(np.dot(af, hf) / denom))
    return float(max(0.0, min(1.0, 1.0 - corr)))


def _concentration(omega: np.ndarray) -> float:
    density = np.sum(omega * omega, axis=-1)
    mean = float(np.mean(density))
    if mean <= EPS:
        return 0.0
    return float(np.max(density) / mean)


def _classify_residue(
    stretch_density: np.ndarray,
    beltrami_defect: float,
    coherence_defect: float,
    pressure_decorrelation: float,
    *,
    beltrami_threshold: float,
    coherence_threshold: float,
    pressure_threshold: float,
) -> tuple[float, float, float]:
    density = np.abs(stretch_density)
    total = float(np.sum(density))
    if total <= EPS:
        return 0.0, 1.0, 0.0
    coherent = (1.0 - coherence_defect) >= coherence_threshold
    non_beltrami = beltrami_defect >= beltrami_threshold
    pressure_decorrelated = pressure_decorrelation >= pressure_threshold
    positive = stretch_density > 0.0
    if pressure_decorrelated:
        rminus = float(np.sum(density) / total)
        return rminus, 1.0 - rminus, 0.0
    if coherent and non_beltrami:
        rplus = float(np.sum(density[positive]) / total)
        rminus = float(np.sum(density[~positive]) / total)
        rzero = max(0.0, 1.0 - rplus - rminus)
        return rminus, rzero, rplus
    rminus = float(np.sum(density[~positive]) / total) if np.any(~positive) else 0.0
    return rminus, max(0.0, 1.0 - rminus), 0.0


def _finite_slope(xs: list[float], ys: list[float], default: float = 0.0) -> float:
    pairs = [(x, y) for x, y in zip(xs, ys) if math.isfinite(x) and math.isfinite(y) and y > 0.0]
    if len(pairs) < 2:
        return default
    x = np.asarray([p[0] for p in pairs], dtype=np.float64)
    y = np.log2(np.asarray([p[1] for p in pairs], dtype=np.float64))
    slope, _ = np.polyfit(x, y, 1)
    return float(slope)


def _progress(label: str, done: int, total: int, started: float, every: int) -> None:
    if every <= 0 or total <= 0:
        return
    if done < total and done % every != 0:
        return
    elapsed = time_module.perf_counter() - started
    rate = done / max(elapsed, 1e-12)
    remaining = max(0, total - done)
    eta = remaining / max(rate, 1e-12)
    print(
        f"[ns-harness] {label} progress={done}/{total} "
        f"elapsed={elapsed:.2f}s rate={rate:.2f} rows/s eta={eta:.2f}s",
        flush=True,
    )


def _rows_for_2d_scalar(omega: np.ndarray, steps: np.ndarray, meta: dict[str, Any], args: argparse.Namespace) -> tuple[list[HarnessRow], dict[str, Any]]:
    dt = float(meta.get("dt", 1.0))
    nu = _effective_nu(meta, args.nu)
    shells = _dyadic_shells(tuple(omega.shape[1:]))
    max_shell = int(shells.max())
    rows: list[HarnessRow] = []
    total = int(omega.shape[0]) * (max_shell + 1)
    started = time_module.perf_counter()
    done = 0
    for ti, frame in enumerate(omega):
        time = float(steps[ti]) * dt if ti < len(steps) else float(ti) * dt
        for k in range(max_shell + 1):
            mask = shells == k
            omega_k = _shell_filter_scalar(frame, mask)
            omega_l2 = float(np.mean(omega_k * omega_k))
            d_k = float(nu * (2.0 ** (2.0 * k)) * omega_l2)
            rows.append(
                HarnessRow(
                    K=k,
                    t=time,
                    omega_l2_sq=omega_l2,
                    D_K=d_k,
                    T_K=0.0,
                    Q_K=0.0,
                    Rminus_K=0.0,
                    Rzero_K=1.0,
                    Rplus_K=0.0,
                    netResidue_K=0.0,
                    BeltramiDefect_K=0.0,
                    DirectionCoherenceDefect_K=1.0,
                    PressureDecorrelationScore_K=1.0,
                    AlignedConcentration_K=float(np.max(omega_k * omega_k) / max(float(np.mean(omega_k * omega_k)), EPS)),
                    M_plus_minus=0.0,
                    M_plus_zero=0.0,
                    M_plus_plus=0.0,
                    s_K=0.0,
                    s_eff_K=0.0,
                    weighted_s_eff_K=0.0,
                    C_K=0.0,
                    gamma_K=0.0,
                    eta_K=0.0,
                    p=int(args.p),
                    beta_K=0.0,
                    theta=float(args.theta),
                    budget_K=0.0,
                    rho_K=0.0,
                    passBudget=0,
                    diagnostic_mode="2d_scalar_fail_closed_no_3d_stretching",
                )
            )
            done += 1
            _progress("2d", done, total, started, int(args.progress_every))
    summary = {
        "diagnostic_mode": "2d_scalar_fail_closed_no_3d_stretching",
        "physical_bridge_available": False,
        "reason": "input is 2D scalar vorticity; exact 3D vortex stretching is unavailable and the 2D embedded stretching term is zero",
        "evidence_only": True,
        "clay_promotion": False,
        "shell_convention": "dyadic",
        "velocity_source": "unavailable_2d_scalar",
    }
    return rows, summary


def _rows_for_3d_vector(
    omega: np.ndarray,
    velocity: np.ndarray | None,
    steps: np.ndarray,
    meta: dict[str, Any],
    args: argparse.Namespace,
) -> tuple[list[HarnessRow], dict[str, Any]]:
    dt = float(meta.get("dt", 1.0))
    nu = _effective_nu(meta, args.nu)
    shells, shell_convention = _shells_for_shape(tuple(omega.shape[1:-1]), meta, args)
    max_shell = int(shells.max())
    preliminary: list[dict[str, Any]] = []
    total = int(omega.shape[0]) * (max_shell + 1)
    started = time_module.perf_counter()
    done = 0
    for ti, frame in enumerate(omega):
        time = float(steps[ti]) * dt if ti < len(steps) else float(ti) * dt
        u = velocity[ti] if velocity is not None else _curl_inverse_velocity(frame)
        pressure_lap = _pressure_laplacian(u)
        for k in range(max_shell + 1):
            mask = shells == k
            omega_k = _shell_filter_vector(frame, mask)
            u_k = _shell_filter_vector(u, mask)
            h_k = _shell_filter_scalar(pressure_lap, mask)
            s_k_tensor = _strain_tensor(u_k)
            s_omega = np.einsum("...ij,...j->...i", s_k_tensor, omega_k)
            stretch_density = np.einsum("...i,...i->...", s_omega, omega_k)
            t_k = abs(float(np.mean(stretch_density)))
            omega_l2 = _l2_sq(omega_k)
            d_k = float(nu * (2.0 ** (2.0 * k)) * omega_l2)
            q_k = float(t_k / (2.0 ** (0.5 * k) * d_k + float(args.eps)))
            beltrami = _beltrami_defect(u_k, omega_k)
            coherence_defect = _coherence_defect(omega_k)
            pressure_decorrelation = _decorrelation_score(stretch_density, h_k)
            concentration = _concentration(omega_k)
            rminus, rzero, rplus = _classify_residue(
                stretch_density,
                beltrami,
                coherence_defect,
                pressure_decorrelation,
                beltrami_threshold=float(args.beltrami_threshold),
                coherence_threshold=float(args.coherence_threshold),
                pressure_threshold=float(args.pressure_decorrelation_threshold),
            )
            c_k = float(q_k / (rplus * (concentration ** float(args.theta)) + float(args.eps)))
            preliminary.append(
                {
                    "K": k,
                    "t": time,
                    "omega_l2_sq": omega_l2,
                    "D_K": d_k,
                    "T_K": t_k,
                    "Q_K": q_k,
                    "Rminus_K": rminus,
                    "Rzero_K": rzero,
                    "Rplus_K": rplus,
                    "netResidue_K": rplus - rminus,
                    "BeltramiDefect_K": beltrami,
                    "DirectionCoherenceDefect_K": coherence_defect,
                    "PressureDecorrelationScore_K": pressure_decorrelation,
                    "AlignedConcentration_K": concentration,
                    "C_K": c_k,
                }
            )
            done += 1
            _progress("3d", done, total, started, int(args.progress_every))

    by_time: dict[float, list[dict[str, Any]]] = {}
    for row in preliminary:
        by_time.setdefault(float(row["t"]), []).append(row)
    enriched: list[HarnessRow] = []
    for time, time_rows in by_time.items():
        time_rows.sort(key=lambda r: int(r["K"]))
        conc_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["AlignedConcentration_K"]) for r in time_rows])
        rplus_slope = _finite_slope([float(r["K"]) for r in time_rows], [float(r["Rplus_K"]) + EPS for r in time_rows])
        beta = max(0.0, conc_slope)
        gamma = max(0.0, -rplus_slope)
        eta = 0.0
        for idx, row in enumerate(time_rows):
            k = int(row["K"])
            next_rplus = float(time_rows[idx + 1]["Rplus_K"]) if idx + 1 < len(time_rows) else 0.0
            rho = float(next_rplus / (float(row["Rplus_K"]) + float(args.eps)))
            mpp = rho
            s_k = max(0.0, next_rplus - mpp * float(row["Rplus_K"])) if idx + 1 < len(time_rows) else 0.0
            mpm = 0.0
            mpz = 0.0
            s_eff = mpm * float(row["Rminus_K"]) + mpz * float(row["Rzero_K"]) + s_k
            budget = gamma + eta * math.log2(float(args.p)) - float(args.theta) * beta
            enriched.append(
                HarnessRow(
                    K=k,
                    t=time,
                    omega_l2_sq=float(row["omega_l2_sq"]),
                    D_K=float(row["D_K"]),
                    T_K=float(row["T_K"]),
                    Q_K=float(row["Q_K"]),
                    Rminus_K=float(row["Rminus_K"]),
                    Rzero_K=float(row["Rzero_K"]),
                    Rplus_K=float(row["Rplus_K"]),
                    netResidue_K=float(row["netResidue_K"]),
                    BeltramiDefect_K=float(row["BeltramiDefect_K"]),
                    DirectionCoherenceDefect_K=float(row["DirectionCoherenceDefect_K"]),
                    PressureDecorrelationScore_K=float(row["PressureDecorrelationScore_K"]),
                    AlignedConcentration_K=float(row["AlignedConcentration_K"]),
                    M_plus_minus=mpm,
                    M_plus_zero=mpz,
                    M_plus_plus=mpp,
                    s_K=s_k,
                    s_eff_K=s_eff,
                    weighted_s_eff_K=float((2.0 ** (0.5 * k)) * s_eff),
                    C_K=float(row["C_K"]),
                    gamma_K=gamma,
                    eta_K=eta,
                    p=int(args.p),
                    beta_K=beta,
                    theta=float(args.theta),
                    budget_K=budget,
                    rho_K=rho,
                    passBudget=1 if budget > 0.5 else 0,
                    diagnostic_mode="3d_vector_direct_spectral",
                )
            )
    summary = {
        "diagnostic_mode": "3d_vector_direct_spectral",
        "physical_bridge_available": True,
        "transition_lineage_available": False,
        "transition_note": "M_plus_plus/rho and s_eff are shell-ratio diagnostics, not particle lineage estimates",
        "evidence_only": True,
        "clay_promotion": False,
        "shell_convention": shell_convention,
        "velocity_source": "velocity_snapshots" if velocity is not None else "curl_inverse_from_omega",
    }
    return enriched, summary


def _write_csv(path: Path, rows: Iterable[HarnessRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(HarnessRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _fmt(value: float | str | None) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    if not math.isfinite(value):
        return ""
    return format(float(value), ".17g")


def _tail_k_star_from_meta(meta: dict[str, Any]) -> int | None:
    ev5_manifest = meta.get("ev5_manifest")
    if isinstance(ev5_manifest, dict):
        value = ev5_manifest.get("tail_k_star")
        if value is not None:
            try:
                return int(math.floor(float(value)))
            except Exception:
                return None
    if "k_star" in meta and meta["k_star"] is not None:
        try:
            return int(math.floor(float(meta["k_star"])))
        except Exception:
            return None
    return None


def _tail_k_star_source(meta: dict[str, Any]) -> str:
    ev5_manifest = meta.get("ev5_manifest")
    if isinstance(ev5_manifest, dict) and ev5_manifest.get("tail_k_star") is not None:
        return "ev5_manifest.tail_k_star"
    if meta.get("k_star") is not None:
        return "meta_json.k_star"
    return "default_zero"


def _bridge_budget_rows(rows: list[HarnessRow], meta: dict[str, Any]) -> tuple[list[BridgeBudgetRow], dict[str, Any]]:
    by_time: dict[float, list[HarnessRow]] = {}
    for row in rows:
        by_time.setdefault(float(row.t), []).append(row)
    times = sorted(by_time)
    tail_by_time_k: dict[tuple[float, int], float] = {}
    tail_d_by_time_k: dict[tuple[float, int], float] = {}
    max_shell = max((r.K for r in rows), default=-1)
    for time in times:
        time_rows = sorted(by_time[time], key=lambda r: r.K)
        for k in range(max_shell + 1):
            tail = [r for r in time_rows if r.K >= k]
            tail_by_time_k[(time, k)] = float(sum(r.omega_l2_sq for r in tail))
            tail_d_by_time_k[(time, k)] = float(sum(r.D_K for r in tail))

    physical = any(r.diagnostic_mode == "3d_vector_direct_spectral" for r in rows)
    k_star = _tail_k_star_from_meta(meta)
    if k_star is None:
        k_star = 0
    nonzero_high_shells = sorted({r.K for r in rows if r.K >= k_star and r.omega_l2_sq > EPS})
    high_shell_support_pass = len(nonzero_high_shells) >= 5
    dt_values = [b - a for a, b in zip(times, times[1:]) if b > a]
    default_dt = min(dt_values) if dt_values else float(meta.get("dt", 1.0))

    out: list[BridgeBudgetRow] = []
    for time_index, time in enumerate(times):
        time_rows = sorted(by_time[time], key=lambda r: r.K)
        next_time = times[time_index + 1] if time_index + 1 < len(times) else None
        for row in time_rows:
            tail = tail_by_time_k[(time, row.K)]
            tail_d = tail_d_by_time_k[(time, row.K)]
            theta_ns: float | None = None
            if next_time is not None and tail_d > EPS:
                dt = max(next_time - time, EPS)
                tail_next = tail_by_time_k.get((next_time, row.K), tail)
                theta_ns = abs(((tail_next - tail) / dt) + tail_d) / tail_d

            adjusted: float | None = None
            if row.Rplus_K > EPS and row.AlignedConcentration_K > EPS:
                adjusted = row.Q_K / (row.Rplus_K * (row.AlignedConcentration_K ** row.theta) + EPS)

            unavailable: list[str] = []
            field_status = "measured_direct_3d_spectral_proxy_lineage"
            if not physical:
                field_status = "blocked_no_3d_vortex_stretching"
                unavailable.append("input is 2D scalar vorticity; literal 3D omega dot grad(u) omega is unavailable")
            if theta_ns is None:
                unavailable.append("theta_NS_K unavailable on final sample or zero tail dissipation")
            if adjusted is None:
                if row.Rplus_K <= EPS:
                    unavailable.append("adjusted_bridge_ratio unavailable because R_plus_K_proxy is zero")
                elif row.AlignedConcentration_K <= EPS:
                    unavailable.append("adjusted_bridge_ratio unavailable because concentration is zero")
                else:
                    unavailable.append("adjusted_bridge_ratio unavailable")
            if not high_shell_support_pass:
                unavailable.append("fewer than five nonzero shells at or above K_star")

            if not physical:
                promotion = "NO_PROMOTION_BLOCKED_NO_3D_STRETCHING"
            elif not high_shell_support_pass:
                promotion = "NO_PROMOTION_HIGH_SHELL_SUPPORT_FAIL"
            elif row.budget_K <= 0.5:
                promotion = "NO_PROMOTION_BUDGET_FAIL"
            elif adjusted is None:
                promotion = "NO_PROMOTION_BRIDGE_RATIO_UNAVAILABLE"
            else:
                promotion = "NO_PROMOTION_DIAGNOSTIC_ONLY"

            step = int(round(time / max(default_dt, EPS)))
            out.append(
                BridgeBudgetRow(
                    step=step,
                    time=float(time),
                    K=int(row.K),
                    shell_enstrophy=float(row.omega_l2_sq),
                    tail_enstrophy=float(tail),
                    D_K=float(row.D_K),
                    theta_NS_K=_fmt(theta_ns),
                    Q_K_proxy=_fmt(row.Q_K),
                    R_plus_K_proxy=_fmt(row.Rplus_K),
                    aligned_concentration_K=_fmt(row.AlignedConcentration_K),
                    beta_hat_K=_fmt(row.beta_K),
                    gamma_hat_K=_fmt(row.gamma_K),
                    eta_hat_K=_fmt(row.eta_K),
                    budget_hat_K=_fmt(row.budget_K),
                    adjusted_bridge_ratio=_fmt(adjusted),
                    promotion_status=promotion,
                    field_status=field_status,
                    unavailable_reason="; ".join(unavailable),
                    diagnostic_mode=row.diagnostic_mode,
                )
            )

    ratios_by_time: dict[float, list[float]] = {}
    for row in out:
        if row.adjusted_bridge_ratio:
            ratios_by_time.setdefault(row.time, []).append(float(row.adjusted_bridge_ratio))
    ratio_increases = sum(
        1
        for values in ratios_by_time.values()
        for a, b in zip(values, values[1:])
        if b > a
    )
    summary = {
        "bridge_budget_table_available": True,
        "k_star": int(k_star),
        "k_star_source": _tail_k_star_source(meta),
        "nonzero_shells_at_or_above_k_star": nonzero_high_shells,
        "high_shell_support_pass": high_shell_support_pass,
        "adjusted_bridge_ratio_shell_increases": int(ratio_increases),
        "adjusted_bridge_ratio_growth_fail": bool(ratio_increases > 0),
        "bridge_ratio_status": "measured" if ratios_by_time else "unavailable_zero_rplus_or_concentration",
        "bridge_budget_field_contract": [
            "step",
            "time",
            "K",
            "shell_enstrophy",
            "tail_enstrophy",
            "D_K",
            "theta_NS_K",
            "Q_K_proxy",
            "R_plus_K_proxy",
            "aligned_concentration_K",
            "beta_hat_K",
            "gamma_hat_K",
            "eta_hat_K",
            "budget_hat_K",
            "adjusted_bridge_ratio",
            "promotion_status",
        ],
    }
    return out, summary


def _write_bridge_budget_csv(path: Path, rows: Iterable[BridgeBudgetRow]) -> None:
    rows = list(rows)
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(BridgeBudgetRow.__dataclass_fields__.keys()))
        writer.writeheader()
        for row in rows:
            writer.writerow(row.__dict__)


def _checks(rows: list[HarnessRow], mode_summary: dict[str, Any]) -> dict[str, Any]:
    finite_c = [r.C_K for r in rows if math.isfinite(r.C_K)]
    finite_mpp = [r.M_plus_plus for r in rows if math.isfinite(r.M_plus_plus)]
    weighted = [r.weighted_s_eff_K for r in rows if math.isfinite(r.weighted_s_eff_K)]
    budgets = [r.budget_K for r in rows if math.isfinite(r.budget_K)]
    sup_c = max(finite_c) if finite_c else math.inf
    sup_mpp = max(finite_mpp) if finite_mpp else math.inf
    source_sum = float(sum(weighted)) if weighted else math.inf
    inf_budget = min(budgets) if budgets else -math.inf
    bridge_available = bool(mode_summary.get("physical_bridge_available", False))
    persistence_pass = bool(sup_mpp < 1.0 / math.sqrt(2.0))
    budget_pass = bool(inf_budget > 0.5)
    promotion_status = "NO_PROMOTION_DIAGNOSTIC_ONLY"
    if bridge_available and not budget_pass:
        promotion_status = "NO_PROMOTION_BUDGET_FAIL"
    checks = {
        **mode_summary,
        "sup_C_K": float(sup_c),
        "sup_M_plus_plus": float(sup_mpp),
        "weighted_source_partial_sum": source_sum,
        "inf_budget_K": float(inf_budget),
        "bridgeTest_finite_on_observed_grid": bool(math.isfinite(sup_c)) if bridge_available else False,
        "persistenceTest_observed": persistence_pass if bridge_available else False,
        "sourceSummabilityTest_finite_prefix": bool(math.isfinite(source_sum)) if bridge_available else False,
        "budgetTest_observed": budget_pass if bridge_available else False,
        "pass": bool(bridge_available and math.isfinite(sup_c) and persistence_pass and math.isfinite(source_sum) and budget_pass),
        "fail_type_1_fake_residue": bool(bridge_available and not math.isfinite(sup_c)),
        "fail_type_2_red_persists": bool(bridge_available and not persistence_pass),
        "fail_type_3_weighted_source_diverges": bool(bridge_available and not math.isfinite(source_sum)),
        "fail_type_4_budget_fails": bool(bridge_available and not budget_pass),
        "promotion_status": promotion_status,
        "clay_navier_stokes_promoted": False,
    }
    if not bridge_available:
        checks["fail_closed_reason"] = mode_summary.get("reason", "physical bridge unavailable")
    return checks


def main() -> None:
    args = parse_args()
    omega, velocity, steps, meta, source = _load_truth(args)
    if omega.ndim == 3:
        rows, summary = _rows_for_2d_scalar(omega, steps, meta, args)
    elif omega.ndim == 5 and omega.shape[-1] == 3:
        rows, summary = _rows_for_3d_vector(omega, velocity, steps, meta, args)
    else:
        raise SystemExit(
            "omega_snapshots must be 2D scalar (T,N,N) or 3D vector (T,N,N,N,3); "
            f"got shape {omega.shape}"
        )

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "ns_diagnostic_table.csv"
    bridge_csv_path = args.out_dir / "ns_bridge_budget_table.csv"
    checks_path = args.out_dir / "ns_diagnostic_checks.json"
    manifest_path = args.out_dir / "ns_diagnostic_manifest.json"
    _write_csv(csv_path, rows)
    bridge_rows, bridge_summary = _bridge_budget_rows(rows, meta)
    _write_bridge_budget_csv(bridge_csv_path, bridge_rows)
    checks = _checks(rows, summary)
    checks.update(bridge_summary)
    manifest = {
        "source": source,
        "meta": meta,
        "row_count": len(rows),
        "bridge_budget_row_count": len(bridge_rows),
        "outputs": {
            "table": str(csv_path),
            "bridge_budget_table": str(bridge_csv_path),
            "checks": str(checks_path),
            "manifest": str(manifest_path),
        },
        "receipt_alignment": "DASHI.Physics.Closure.ClaySprintFortyTwoNSDiagnosticHarnessReceipt",
        "evidence_boundary": "diagnostic harness only; no Navier-Stokes theorem or Clay promotion",
    }
    checks_path.write_text(json.dumps(checks, indent=2, allow_nan=True), encoding="utf-8")
    manifest_path.write_text(json.dumps(manifest, indent=2, allow_nan=True), encoding="utf-8")
    print(f"[ns-harness] wrote {csv_path}, {bridge_csv_path}, {checks_path}, {manifest_path}")
    print(
        "[ns-harness] "
        f"mode={checks.get('diagnostic_mode')} pass={checks.get('pass')} "
        f"sup_C_K={checks.get('sup_C_K')} inf_budget_K={checks.get('inf_budget_K')} "
        f"promotion={checks.get('promotion_status')}"
    )


if __name__ == "__main__":
    main()
