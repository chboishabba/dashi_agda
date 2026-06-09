#!/usr/bin/env python3
"""Pure-stdlib NS S2 cascade-width diagnostic harness.

This is a finite sampled diagnostic only.  It tests the exact angular
Biot-Savart/Leray eigenbundle machinery when available, reports lambda
distributions for the triadic zero-mode product, and estimates depth-1/depth-2
output width over several thresholds.  It is not a PDE proof, theorem
promotion, or Clay receipt.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import statistics
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable, Sequence


Vec3 = tuple[float, float, float]

EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
REQUESTED_PROVIDER = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"
FALLBACK_PROVIDER = SCRIPT_DIR / "ns_exact_strain_eigenbundle.py"
DEFAULT_THRESHOLDS = (0.01, 0.02, 0.05, 0.1, 0.2)


@dataclass(frozen=True)
class Provider:
    module: ModuleType | None
    source: str
    requested_provider_present: bool
    fallback_provider_used: bool
    notes: tuple[str, ...]


@dataclass(frozen=True)
class Frame:
    c: Vec3
    e_plus: Vec3
    omega: Vec3


@dataclass(frozen=True)
class LambdaRecord:
    lam: float
    family_i_factor: float
    family_ii_factor: float
    family: str
    c: Vec3


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--samples", type=int, default=12000)
    parser.add_argument("--continuations", type=int, default=120)
    parser.add_argument("--normals", type=int, default=384)
    parser.add_argument("--thresholds", default=",".join(str(x) for x in DEFAULT_THRESHOLDS))
    parser.add_argument(
        "--polarization-model",
        choices=("canonical", "seeded", "helical-plus", "helical-minus"),
        default="canonical",
        help="Input polarization model passed to the exact finite provider.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON only.")
    return parser.parse_args(argv)


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u: Vec3, v: Vec3) -> Vec3:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def sub(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


def norm_sq(u: Vec3) -> float:
    return dot(u, u)


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, norm_sq(u)))


def normalize(u: Vec3, eps: float = EPS) -> Vec3 | None:
    n = norm(u)
    if n <= eps:
        return None
    return scale(1.0 / n, u)


def project_tangent(k: Vec3, v: Vec3) -> Vec3 | None:
    k2 = norm_sq(k)
    if k2 <= EPS * EPS:
        return None
    return sub(v, scale(dot(v, k) / k2, k))


def coerce_vec3(value: Any) -> Vec3 | None:
    if isinstance(value, (tuple, list)) and len(value) == 3:
        try:
            xs = (float(value[0]), float(value[1]), float(value[2]))
        except (TypeError, ValueError):
            return None
        if all(math.isfinite(x) for x in xs):
            return xs
    return None


def parse_thresholds(raw: str) -> tuple[float, ...]:
    values: list[float] = []
    for part in raw.split(","):
        item = part.strip()
        if not item:
            continue
        value = float(item)
        if value < 0.0:
            raise ValueError("--thresholds must be nonnegative")
        values.append(value)
    if not values:
        raise ValueError("--thresholds must contain at least one value")
    return tuple(sorted(set(values)))


def load_module(path: Path, name: str) -> ModuleType | None:
    if not path.exists():
        return None
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        return None
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load_provider() -> Provider:
    requested = load_module(REQUESTED_PROVIDER, "ns_s2_biot_savart_eigenbundle")
    if requested is not None:
        return Provider(
            module=requested,
            source=str(REQUESTED_PROVIDER),
            requested_provider_present=True,
            fallback_provider_used=False,
            notes=("loaded requested S2 Biot-Savart eigenbundle provider",),
        )

    fallback = load_module(FALLBACK_PROVIDER, "ns_exact_strain_eigenbundle")
    if fallback is not None:
        return Provider(
            module=fallback,
            source=str(FALLBACK_PROVIDER),
            requested_provider_present=False,
            fallback_provider_used=True,
            notes=(
                "requested scripts/ns_s2_biot_savart_eigenbundle.py was absent",
                "used scripts/ns_exact_strain_eigenbundle.py finite Leray/Biot-Savart provider",
            ),
        )

    return Provider(
        module=None,
        source="internal-pure-stdlib-fallback",
        requested_provider_present=False,
        fallback_provider_used=False,
        notes=(
            "requested and fallback exact providers were absent",
            "used internal angular formula fallback; treat as diagnostic only",
        ),
    )


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def fibonacci_sphere(count: int) -> list[Vec3]:
    if count <= 0:
        raise ValueError("sphere sample count must be positive")
    points: list[Vec3] = []
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    for k in range(count):
        z = 1.0 - 2.0 * (k + 0.5) / count
        r = math.sqrt(max(0.0, 1.0 - z * z))
        theta = golden_angle * k
        points.append((r * math.cos(theta), r * math.sin(theta), z))
    return points


def tangent_basis(c: Vec3) -> tuple[Vec3, Vec3] | None:
    axes: tuple[Vec3, Vec3, Vec3] = (
        (1.0, 0.0, 0.0),
        (0.0, 1.0, 0.0),
        (0.0, 0.0, 1.0),
    )
    best: Vec3 | None = None
    best_norm = -1.0
    for axis in axes:
        projected = project_tangent(c, axis)
        if projected is None:
            continue
        size = norm_sq(projected)
        if size > best_norm:
            best = projected
            best_norm = size
    if best is None:
        return None
    e1 = normalize(best)
    if e1 is None:
        return None
    e2 = normalize(cross(c, e1))
    if e2 is None:
        return None
    return e1, e2


def internal_s2_frame(c: Vec3) -> tuple[Vec3, Vec3] | None:
    """Fallback for the angular m11/m12 eigenline recorded in the prompt."""

    c_hat = normalize(c)
    if c_hat is None:
        return None
    basis = tangent_basis(c_hat)
    if basis is None:
        return None
    e_theta, e_phi = basis

    x, y, z = c_hat
    phi = math.atan2(y, x)
    psi = math.acos(max(-1.0, min(1.0, z)))
    m11 = 0.5 * (math.cos(psi) ** 2 - (math.sin(psi) ** 2) * math.cos(2.0 * phi))
    m12 = -0.5 * (math.sin(psi) ** 2) * math.sin(2.0 * phi)
    beta = 0.5 * math.atan2(m12, m11)
    e_plus = normalize(add(scale(math.cos(beta), e_theta), scale(math.sin(beta), e_phi)))
    if e_plus is None:
        return None
    omega = normalize(cross(c_hat, e_plus))
    if omega is None:
        return None
    return e_plus, omega


def provider_frame(
    provider: Provider,
    a: Vec3,
    b: Vec3,
    c: Vec3,
    polarization_model: str,
    seed: int,
) -> Frame | None:
    module = provider.module
    if module is None:
        raw = internal_s2_frame(c)
        if raw is None:
            return None
        e_plus, omega = raw
        return Frame(c=c, e_plus=e_plus, omega=omega)

    for fn_name in ("lambda_ns_triad", "ns_lambda_triad", "triad_lambda"):
        fn = getattr(module, fn_name, None)
        if callable(fn):
            # The caller computes lambda itself for uniform reporting, but if
            # the requested provider exists and exposes only a lambda API, use
            # an adjacent frame API if available or fall through.
            break

    for fn_name in (
        "output_frame",
        "exact_output_frame",
        "strain_frame",
        "frame_for_triad",
        "compute_frame",
    ):
        fn = getattr(module, fn_name, None)
        if not callable(fn):
            continue
        result = None
        for kwargs in (
            {
                "a": a,
                "b": b,
                "c": c,
                "polarization_model": polarization_model,
                "polarization_seed": seed,
            },
            {"a": a, "b": b, "c": c},
        ):
            try:
                result = fn(**kwargs)
                break
            except TypeError:
                continue
        if result is None:
            try:
                result = fn(a, b, c)
            except TypeError:
                try:
                    result = fn(a, b)
                except TypeError:
                    result = None
        frame = frame_from_payload(result, c)
        if frame is not None:
            return frame

    triadic = getattr(module, "triadic_strain_eigenbundle_from_models", None)
    if callable(triadic):
        model_map = {
            "canonical": ("e1", "e2", 0.0, 0.0),
            "seeded": (
                "angle",
                "angle",
                math.sin(0.017 * seed + dot(a, c)) * math.pi,
                math.sin(0.019 * seed + dot(b, c) + 0.5) * math.pi,
            ),
            "helical-plus": ("plus45", "plus45", 0.0, 0.0),
            "helical-minus": ("minus45", "minus45", 0.0, 0.0),
        }
        model_a, model_b, angle_a, angle_b = model_map[polarization_model]
        result = triadic(
            a,
            b,
            model_a=model_a,
            model_b=model_b,
            angle_a=angle_a,
            angle_b=angle_b,
            symmetrized=True,
        )
        frame = frame_from_payload(result, c)
        if frame is not None:
            return frame

    raw = internal_s2_frame(c)
    if raw is None:
        return None
    e_plus, omega = raw
    return Frame(c=c, e_plus=e_plus, omega=omega)


def frame_from_payload(payload: Any, c: Vec3) -> Frame | None:
    if payload is None:
        return None
    if isinstance(payload, dict):
        e_plus = coerce_vec3(payload.get("e_plus") or payload.get("stretching") or payload.get("strain"))
        omega = coerce_vec3(payload.get("omega") or payload.get("omega_out") or payload.get("vorticity"))
    elif isinstance(payload, (list, tuple)) and len(payload) >= 2:
        e_plus = coerce_vec3(payload[0])
        omega = coerce_vec3(payload[1])
    else:
        strain = getattr(payload, "strain", payload)
        e_plus = coerce_vec3(getattr(strain, "e_plus", None))
        omega = coerce_vec3(getattr(strain, "omega_out", None))

    c_hat = normalize(c)
    if c_hat is None:
        return None
    e_plus = normalize(e_plus) if e_plus is not None else None
    if e_plus is None:
        return None
    omega = normalize(project_tangent(c_hat, omega)) if omega is not None else normalize(cross(c_hat, e_plus))
    if omega is None:
        return None
    return Frame(c=c_hat, e_plus=e_plus, omega=omega)


def direct_provider_lambda_record(provider: Provider, a: Vec3, b: Vec3) -> LambdaRecord | None:
    module = provider.module
    if module is None:
        return None
    fn = getattr(module, "lambda_ns_triad", None)
    if not callable(fn):
        return None
    try:
        payload = fn(a, b)
    except TypeError:
        return None
    if payload is None:
        return None

    c = coerce_vec3(getattr(payload, "c", None))
    if c is None and isinstance(payload, dict):
        c = coerce_vec3(payload.get("c"))
    if c is None:
        c = normalize(add(a, b))
    if c is None:
        return None

    def get_float(attr: str, key: str | None = None) -> float | None:
        value = getattr(payload, attr, None)
        if value is None and isinstance(payload, dict):
            value = payload.get(key or attr)
        try:
            out = float(value)
        except (TypeError, ValueError):
            return None
        return out if math.isfinite(out) else None

    lam = get_float("lambda_value")
    family_i_factor = get_float("transverse_b_factor")
    family_ii_factor = get_float("a_alignment_factor")
    if lam is None or family_i_factor is None or family_ii_factor is None:
        return None

    residuals = getattr(payload, "residuals", None)
    family = getattr(residuals, "hit_family", None)
    if family is None and isinstance(payload, dict):
        residual_payload = payload.get("residuals")
        if isinstance(residual_payload, dict):
            family = residual_payload.get("hit_family")
    if family not in ("family_i", "family_ii", "both"):
        if family_i_factor < family_ii_factor:
            family = "family_i"
        elif family_ii_factor < family_i_factor:
            family = "family_ii"
        else:
            family = "both"

    return LambdaRecord(
        lam=max(0.0, lam),
        family_i_factor=max(0.0, family_i_factor),
        family_ii_factor=max(0.0, family_ii_factor),
        family=str(family),
        c=normalize(c) or c,
    )


def lambda_ns_triad(provider: Provider, a: Vec3, b: Vec3, seed: int, polarization_model: str) -> LambdaRecord | None:
    direct = direct_provider_lambda_record(provider, a, b)
    if direct is not None:
        return direct

    c = normalize(add(a, b))
    if c is None:
        return None
    frame = provider_frame(provider, a, b, c, polarization_model, seed)
    if frame is None:
        return None
    pc_b = project_tangent(c, b)
    if pc_b is None:
        return None
    pc_b_sq = norm_sq(pc_b)
    if pc_b_sq <= EPS * EPS:
        return None

    omega_hat = normalize(project_tangent(c, frame.omega))
    if omega_hat is None:
        return None
    omega_projection_on_pc_b = dot(omega_hat, pc_b)
    family_i_factor = max(0.0, pc_b_sq - omega_projection_on_pc_b * omega_projection_on_pc_b) / pc_b_sq
    family_ii_factor = dot(a, omega_hat) * dot(a, omega_hat)
    lam = max(0.0, family_i_factor * family_ii_factor)
    if family_i_factor < family_ii_factor:
        family = "family_i"
    elif family_ii_factor < family_i_factor:
        family = "family_ii"
    else:
        family = "both"
    return LambdaRecord(lam=lam, family_i_factor=family_i_factor, family_ii_factor=family_ii_factor, family=family, c=c)


def quantiles(values: Sequence[float]) -> dict[str, float | None]:
    finite = sorted(x for x in values if math.isfinite(x))
    if not finite:
        return {"count": 0, "min": None, "p05": None, "p25": None, "median": None, "mean": None, "p75": None, "p95": None, "max": None}

    def pct(q: float) -> float:
        index = min(len(finite) - 1, max(0, int(round(q * (len(finite) - 1)))))
        return finite[index]

    return {
        "count": len(finite),
        "min": finite[0],
        "p05": pct(0.05),
        "p25": pct(0.25),
        "median": statistics.median(finite),
        "mean": statistics.fmean(finite),
        "p75": pct(0.75),
        "p95": pct(0.95),
        "max": finite[-1],
    }


def estimate_width(points: Sequence[Vec3], normals: Sequence[Vec3]) -> dict[str, Any]:
    if not points:
        return {"estimated_width": None, "best_normal": None, "point_count": 0}
    best_width = -1.0
    best_normal = normals[0]
    for normal in normals:
        width = min(abs(dot(normal, point)) for point in points)
        if width > best_width:
            best_width = width
            best_normal = normal
    return {
        "estimated_width": best_width,
        "best_normal": rounded_vec(best_normal),
        "point_count": len(points),
    }


def rounded_vec(u: Vec3, digits: int = 8) -> list[float]:
    return [round(u[0], digits), round(u[1], digits), round(u[2], digits)]


def run_harness(args: argparse.Namespace) -> dict[str, Any]:
    thresholds = parse_thresholds(args.thresholds)
    provider = load_provider()
    rng = random.Random(args.seed)
    normals = fibonacci_sphere(args.normals)
    continuation_pool = fibonacci_sphere(args.continuations)

    records: list[LambdaRecord] = []
    degenerate = 0
    anti_parallel = 0
    family_nearest_counts = {"family_i": 0, "family_ii": 0, "both": 0}

    for index in range(args.samples):
        a = random_unit(rng)
        b = random_unit(rng)
        if norm(add(a, b)) <= EPS:
            anti_parallel += 1
            continue
        record = lambda_ns_triad(provider, a, b, args.seed + index, args.polarization_model)
        if record is None:
            degenerate += 1
            continue
        records.append(record)
        family_nearest_counts[record.family] = family_nearest_counts.get(record.family, 0) + 1

    by_threshold: dict[str, dict[str, Any]] = {}
    lambda_values = [record.lam for record in records]
    family_i_values = [record.family_i_factor for record in records]
    family_ii_values = [record.family_ii_factor for record in records]
    min_threshold = min(thresholds)
    max_threshold = max(thresholds)
    max_depth1 = [record for record in records if record.lam <= max_threshold]
    depth2_best: dict[Vec3, LambdaRecord | None] = {}
    depth2_first_valid: dict[Vec3, LambdaRecord | None] = {}
    depth2_attempts: dict[Vec3, int] = {}
    depth2_degenerates: dict[Vec3, int] = {}

    for idx, record in enumerate(max_depth1):
        best: LambdaRecord | None = None
        first_valid: LambdaRecord | None = None
        attempts = 0
        degenerates = 0
        for continuation_index, d in enumerate(continuation_pool):
            attempts += 1
            nxt = lambda_ns_triad(
                provider,
                record.c,
                d,
                args.seed + 1000003 + idx * 9176 + continuation_index,
                args.polarization_model,
            )
            if nxt is None:
                degenerates += 1
                continue
            if first_valid is None:
                first_valid = nxt
            if best is None or nxt.lam < best.lam:
                best = nxt
            if best.lam <= min_threshold:
                break
        depth2_best[record.c] = best
        depth2_first_valid[record.c] = first_valid
        depth2_attempts[record.c] = attempts
        depth2_degenerates[record.c] = degenerates

    for threshold in thresholds:
        depth1 = [record for record in records if record.lam <= threshold]
        family_hits = {
            "family_i": sum(1 for record in depth1 if record.family_i_factor <= threshold),
            "family_ii": sum(1 for record in depth1 if record.family_ii_factor <= threshold),
            "both": sum(
                1
                for record in depth1
                if record.family_i_factor <= threshold and record.family_ii_factor <= threshold
            ),
        }
        depth2_survivor_outputs: list[Vec3] = []
        random_depth2_survivor_outputs: list[Vec3] = []
        depth2_attempted = sum(depth2_attempts.get(record.c, 0) for record in depth1)
        depth2_degenerate = sum(depth2_degenerates.get(record.c, 0) for record in depth1)
        best_depth2_lambdas: list[float] = []
        first_valid_depth2_lambdas: list[float] = []
        for idx, record in enumerate(depth1):
            del idx
            best = depth2_best.get(record.c)
            if best is not None:
                best_depth2_lambdas.append(best.lam)
                if best.lam <= threshold:
                    depth2_survivor_outputs.append(best.c)
            first_valid = depth2_first_valid.get(record.c)
            if first_valid is not None:
                first_valid_depth2_lambdas.append(first_valid.lam)
                if first_valid.lam <= threshold:
                    random_depth2_survivor_outputs.append(first_valid.c)

        key = f"{threshold:g}"
        by_threshold[key] = {
            "threshold": threshold,
            "depth1_zero_count": len(depth1),
            "depth1_zero_fraction": len(depth1) / len(records) if records else 0.0,
            "family_hit_split": family_hits,
            "depth2_survivor_count": len(depth2_survivor_outputs),
            "depth2_survival_fraction_of_depth1": (
                len(depth2_survivor_outputs) / len(depth1) if depth1 else 0.0
            ),
            "random_depth2_survivor_count_first_valid": len(random_depth2_survivor_outputs),
            "random_depth2_survival_fraction_first_valid": (
                len(random_depth2_survivor_outputs) / len(depth1) if depth1 else 0.0
            ),
            "depth2_attempted_continuations": depth2_attempted,
            "depth2_degenerate_continuations": depth2_degenerate,
            "best_depth2_lambda_distribution": quantiles(best_depth2_lambdas),
            "first_valid_depth2_lambda_distribution": quantiles(first_valid_depth2_lambdas),
            "depth1_output_width": estimate_width([record.c for record in depth1], normals),
            "depth2_output_width": estimate_width(depth2_survivor_outputs, normals),
            "random_depth2_output_width_first_valid": estimate_width(
                random_depth2_survivor_outputs,
                normals,
            ),
        }

    return {
        "scope": "finite_sampled_ns_s2_biot_savart_leray_cascade_diagnostic_not_proof",
        "promotion": False,
        "clay_promoted": False,
        "parameters": {
            "seed": args.seed,
            "samples": args.samples,
            "continuations": args.continuations,
            "normals": args.normals,
            "thresholds": list(thresholds),
            "polarization_model": args.polarization_model,
        },
        "provider": {
            "source": provider.source,
            "requested_provider_present": provider.requested_provider_present,
            "fallback_provider_used": provider.fallback_provider_used,
            "notes": list(provider.notes),
        },
        "counts": {
            "accepted": len(records),
            "anti_parallel_rejects": anti_parallel,
            "degenerate_or_missing_frame": degenerate,
            "family_nearest_split_all": family_nearest_counts,
        },
        "lambda_distribution": quantiles(lambda_values),
        "family_i_factor_distribution": quantiles(family_i_values),
        "family_ii_factor_distribution": quantiles(family_ii_values),
        "threshold_reports": by_threshold,
        "interpretation": (
            "Depth-2 survivor counts are based on the best lambda over the sampled continuation pool; "
            "random_depth2_* counts use only the first valid continuation in that pool. "
            "Width is estimated as sup_n inf_c |n.c| over sampled candidate normals."
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.continuations <= 0:
        raise ValueError("--continuations must be positive")
    if args.normals <= 0:
        raise ValueError("--normals must be positive")
    summary = run_harness(args)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
