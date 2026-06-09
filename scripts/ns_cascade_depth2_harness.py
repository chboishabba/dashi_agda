#!/usr/bin/env python3
"""Finite falsification probe for NS triadic cascade zero modes.

This is a numerical harness for the boundary target recorded in
NSTrueLerayTriadicZeroModeClassificationBoundary and
NSCascadeClosedZeroModeOutputWidthBoundary.  It does not prove output width.

The probe uses equal-scale resonant triads

    c = normalize(a + b)

and the rank-one zero-mode classification proxy:

    Family I  residual: omega(c) parallel P_c b
    Family II residual: omega(c) orthogonal P_c a

For each single-depth near-zero triad it reuses the output c as the next
input and searches over d for a second-generation near-zero triad

    e = normalize(c + d).

The output report is meant to falsify naive cascade-closure claims, estimate
sampled strip coverage, and identify candidate directions for further exact
symbol calculation.  It intentionally stays finite, sampled, and fail-closed.
"""

from __future__ import annotations

import argparse
import importlib.util
import inspect
import json
import math
import random
import statistics
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

Vec3 = Tuple[float, float, float]


EPS = 1.0e-12
E1: Vec3 = (1.0, 0.0, 0.0)
E2: Vec3 = (0.0, 1.0, 0.0)
E3: Vec3 = (0.0, 0.0, 1.0)


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u: Vec3, v: Vec3) -> Vec3:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def norm(u: Vec3) -> float:
    return math.sqrt(max(dot(u, u), 0.0))


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def normalize(u: Vec3) -> Optional[Vec3]:
    n = norm(u)
    if n <= EPS:
        return None
    return (u[0] / n, u[1] / n, u[2] / n)


def project_tangent(c: Vec3, v: Vec3) -> Vec3:
    return add(v, scale(-dot(c, v), c))


def tangent_frame_omega(c: Vec3, pole_cutoff: float = 1.0e-5) -> Optional[Vec3]:
    """Return a deterministic tangent proxy for output vorticity direction.

    The exact proof needs the true NS strain eigenbundle.  This harness uses
    a canonical tangent frame proxy, returning None near the north/south pole
    where the frame degenerates.  Near-pole exclusions are reported.
    """

    raw = cross(c, E3)
    if norm(raw) <= pole_cutoff:
        return None
    return normalize(raw)


@dataclass(frozen=True)
class FrameModel:
    name: str
    exact_symbol_available: bool
    exact_symbol_source: Optional[str]
    caveats: Tuple[str, ...]
    exact_callable: object = None
    omega_hat_callable: object = None
    residual_callable: object = None
    lambda_callable: object = None


EXACT_STRAIN_FUNCTION_NAMES = (
    "exact_output_omega",
    "finite_ns_output_omega",
    "ns_bilinear_output_omega",
    "output_omega",
    "triadic_strain_eigenbundle_from_models",
)

S2_BIOT_SAVART_OMEGA_FUNCTION_NAMES = (
    "omega_hat",
    "angular_omega_hat",
    "s2_omega_hat",
    "s2_biot_savart_omega_hat",
    "angular_eigenbundle",
    "maximal_strain_vorticity_direction",
    "vorticity_direction",
)

S2_BIOT_SAVART_RESIDUAL_FUNCTION_NAMES = (
    "triadic_residual",
    "angular_triadic_residual",
    "s2_biot_savart_residual",
    "zero_mode_residual",
    "residual_families",
    "evaluate_triad",
    "triadic_lambda_residual",
)

S2_BIOT_SAVART_LAMBDA_FUNCTION_NAMES = (
    "triadic_lambda",
    "angular_triadic_lambda",
    "s2_biot_savart_lambda",
    "lambda_ns_triad",
    "leakage_lambda",
)


def _load_helper_module(helper_name: str) -> tuple[Optional[object], Optional[Path], Tuple[str, ...]]:
    helper_path = Path(__file__).with_name(helper_name)
    if not helper_path.exists():
        return None, helper_path, (f"scripts/{helper_name} is absent",)

    spec = importlib.util.spec_from_file_location(helper_path.stem, helper_path)
    if spec is None or spec.loader is None:
        return None, helper_path, (f"scripts/{helper_name} exists but could not be loaded",)

    module = importlib.util.module_from_spec(spec)
    try:
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
    except Exception as exc:  # pragma: no cover - diagnostic path.
        return (
            None,
            helper_path,
            (
                f"scripts/{helper_name} raised during import",
                f"helper import error: {type(exc).__name__}: {exc}",
            ),
        )
    return module, helper_path, ()


def _first_callable(module: object, names: Sequence[str]) -> tuple[Optional[str], Optional[object]]:
    for name in names:
        candidate = getattr(module, name, None)
        if callable(candidate):
            return name, candidate
    return None, None


def _load_exact_strain_model() -> FrameModel:
    module, helper_path, load_caveats = _load_helper_module("ns_exact_strain_eigenbundle.py")
    if module is None:
        return FrameModel(
            name="exact-strain",
            exact_symbol_available=False,
            exact_symbol_source=str(helper_path) if helper_path is not None else None,
            caveats=(
                *load_caveats,
                "exact-strain residuals fail closed instead of falling back to tangent-proxy",
                "no exact finite NS bilinear-symbol output omega was evaluated",
            ),
        )

    name, candidate = _first_callable(module, EXACT_STRAIN_FUNCTION_NAMES)
    if candidate is not None:
        return FrameModel(
            name="exact-strain",
            exact_symbol_available=True,
            exact_symbol_source=f"{helper_path}:{name}",
            caveats=(
                "exact-strain uses helper-provided finite NS bilinear-symbol "
                "output omega when the helper returns a nondegenerate vector",
                "degenerate, missing, nonfinite, or API-incompatible helper "
                "outputs are counted as omega_missing",
            ),
            exact_callable=candidate,
        )

    return FrameModel(
        name="exact-strain",
        exact_symbol_available=False,
        exact_symbol_source=str(helper_path),
        caveats=(
            "scripts/ns_exact_strain_eigenbundle.py exists but exposes none of "
            f"{', '.join(EXACT_STRAIN_FUNCTION_NAMES)}",
            "exact-strain residuals fail closed on helper-API degeneracy",
        ),
    )


def _load_s2_biot_savart_model() -> FrameModel:
    module, helper_path, load_caveats = _load_helper_module("ns_s2_biot_savart_eigenbundle.py")
    if module is None:
        return FrameModel(
            name="s2-biot-savart",
            exact_symbol_available=False,
            exact_symbol_source=str(helper_path) if helper_path is not None else None,
            caveats=(
                *load_caveats,
                "s2-biot-savart residuals fail closed instead of using output-built omega",
                "angular omega_hat(c), residual, and lambda must come from the helper",
            ),
        )

    omega_name, omega_fn = _first_callable(module, S2_BIOT_SAVART_OMEGA_FUNCTION_NAMES)
    residual_name, residual_fn = _first_callable(module, S2_BIOT_SAVART_RESIDUAL_FUNCTION_NAMES)
    lambda_name, lambda_fn = _first_callable(module, S2_BIOT_SAVART_LAMBDA_FUNCTION_NAMES)

    if omega_fn is None or (residual_fn is None and lambda_fn is None):
        missing = []
        if omega_fn is None:
            missing.append("angular omega_hat(c)")
        if residual_fn is None and lambda_fn is None:
            missing.append("residual/lambda evaluator")
        return FrameModel(
            name="s2-biot-savart",
            exact_symbol_available=False,
            exact_symbol_source=str(helper_path),
            caveats=(
                f"scripts/ns_s2_biot_savart_eigenbundle.py lacks {', '.join(missing)}",
                "s2-biot-savart residuals fail closed instead of using output-built omega",
                "accepted omega names: " + ", ".join(S2_BIOT_SAVART_OMEGA_FUNCTION_NAMES),
                "accepted residual names: " + ", ".join(S2_BIOT_SAVART_RESIDUAL_FUNCTION_NAMES),
                "accepted lambda names: " + ", ".join(S2_BIOT_SAVART_LAMBDA_FUNCTION_NAMES),
            ),
        )

    source_parts = [f"{helper_path}:{omega_name}"]
    if residual_name is not None:
        source_parts.append(f"{helper_path}:{residual_name}")
    if lambda_name is not None:
        source_parts.append(f"{helper_path}:{lambda_name}")

    return FrameModel(
        name="s2-biot-savart",
        exact_symbol_available=True,
        exact_symbol_source="; ".join(source_parts),
        caveats=(
            "s2-biot-savart uses angular omega_hat(c) from "
            "scripts/ns_s2_biot_savart_eigenbundle.py",
            "residual/lambda values come from the helper; the harness does not "
            "reuse output-built omega for this model",
            "missing, nonfinite, or API-incompatible helper outputs are counted as omega_missing",
        ),
        omega_hat_callable=omega_fn,
        residual_callable=residual_fn,
        lambda_callable=lambda_fn,
    )


def make_frame_model(name: str) -> FrameModel:
    if name == "tangent-proxy":
        return FrameModel(
            name="tangent-proxy",
            exact_symbol_available=False,
            exact_symbol_source=None,
            caveats=(
                "tangent-proxy uses a deterministic tangent frame for output "
                "omega and is not the exact NS strain eigenbundle",
                "near-pole tangent-frame degeneracy is counted as omega_missing",
            ),
        )
    if name == "exact-strain":
        return _load_exact_strain_model()
    if name in ("s2-biot-savart", "angular-biot-savart"):
        return _load_s2_biot_savart_model()
    raise ValueError(f"unknown frame model: {name}")


def _vec3_from_payload(payload: object) -> Optional[Vec3]:
    if payload is None:
        return None
    if isinstance(payload, dict):
        for key in (
            "omega",
            "output_omega",
            "omega_out",
            "vorticity",
            "vorticity_direction",
            "omega_hat",
            "strain",
        ):
            if key in payload:
                return _vec3_from_payload(payload[key])
        return None
    for attr in ("omega", "output_omega", "omega_out", "omega_hat", "vorticity_direction"):
        if hasattr(payload, attr):
            return _vec3_from_payload(getattr(payload, attr))
    if hasattr(payload, "strain"):
        return _vec3_from_payload(getattr(payload, "strain"))
    if isinstance(payload, (list, tuple)) and len(payload) == 3:
        try:
            values = (float(payload[0]), float(payload[1]), float(payload[2]))
        except (TypeError, ValueError):
            return None
        if all(math.isfinite(x) for x in values):
            return values
    return None


def exact_strain_omega(a: Vec3, b: Vec3, c: Vec3, model: FrameModel) -> Optional[Vec3]:
    if model.exact_callable is None:
        return None

    fn = model.exact_callable
    call_patterns = ((a, b, c), (a, b), ({"a": a, "b": b, "c": c},))
    try:
        parameters = inspect.signature(fn).parameters
    except (TypeError, ValueError):
        parameters = {}

    for call_args in call_patterns:
        if parameters and len(call_args) > len(parameters):
            continue
        try:
            raw = fn(*call_args)
        except Exception:
            continue
        omega = normalize(_vec3_from_payload(raw) or (0.0, 0.0, 0.0))
        if omega is not None:
            return omega
    return None


def _as_finite_float(value: object) -> Optional[float]:
    try:
        x = float(value)
    except (TypeError, ValueError):
        return None
    if not math.isfinite(x):
        return None
    return x


def _value_from_payload(payload: object, keys: Sequence[str]) -> Optional[float]:
    if payload is None:
        return None
    if isinstance(payload, dict):
        for key in keys:
            if key in payload:
                value = _value_from_payload(payload[key], keys)
                if value is not None:
                    return value
        for value in payload.values():
            nested = _value_from_payload(value, keys)
            if nested is not None:
                return nested
        return None
    for attr in keys:
        if hasattr(payload, attr):
            value = _value_from_payload(getattr(payload, attr), keys)
            if value is not None:
                return value
    for attr in ("residuals", "diagnostic", "result"):
        if hasattr(payload, attr):
            value = _value_from_payload(getattr(payload, attr), keys)
            if value is not None:
                return value
    return _as_finite_float(payload)


def _string_from_payload(payload: object, keys: Sequence[str]) -> Optional[str]:
    if payload is None or isinstance(payload, (int, float, bool)):
        return None
    if isinstance(payload, str):
        return payload
    if isinstance(payload, dict):
        for key in keys:
            value = payload.get(key)
            if isinstance(value, str):
                return value
            if value is not None and not isinstance(value, (int, float, bool, str)):
                nested = _string_from_payload(value, keys)
                if nested is not None:
                    return nested
        for value in payload.values():
            if value is not None and not isinstance(value, (int, float, bool, str)):
                nested = _string_from_payload(value, keys)
                if nested is not None:
                    return nested
    for attr in keys:
        value = getattr(payload, attr, None)
        if isinstance(value, str):
            return value
        if value is not None and not isinstance(value, (int, float, bool, str)):
            nested = _string_from_payload(value, keys)
            if nested is not None:
                return nested
    for attr in ("residuals", "diagnostic", "result"):
        value = getattr(payload, attr, None)
        if value is not None and not isinstance(value, (int, float, bool, str)):
            nested = _string_from_payload(value, keys)
            if nested is not None:
                return nested
    return None


def _call_helper(fn: object, call_patterns: Sequence[tuple]) -> Optional[object]:
    try:
        parameters = inspect.signature(fn).parameters
    except (TypeError, ValueError):
        parameters = {}

    for call_args in call_patterns:
        if parameters and len(call_args) > len(parameters):
            continue
        try:
            return fn(*call_args)
        except Exception:
            continue
    return None


@dataclass(frozen=True)
class AngularResidualPayload:
    residual: float
    family: str
    c: Vec3
    omega_missing: bool
    lambda_value: Optional[float]


def s2_biot_savart_residual(a: Vec3, b: Vec3, model: FrameModel) -> AngularResidualPayload:
    c = normalize(add(a, b))
    if c is None:
        return AngularResidualPayload(float("inf"), "antipodal", (0.0, 0.0, 0.0), True, None)
    if model.omega_hat_callable is None or (
        model.residual_callable is None and model.lambda_callable is None
    ):
        return AngularResidualPayload(float("inf"), "omega-missing", c, True, None)

    omega_raw = _call_helper(
        model.omega_hat_callable,
        ((c,), ({"c": c},), (a, b, c), (a, b)),
    )
    omega = normalize(_vec3_from_payload(omega_raw) or (0.0, 0.0, 0.0))
    if omega is None:
        return AngularResidualPayload(float("inf"), "omega-missing", c, True, None)

    payload = None
    if model.residual_callable is not None:
        payload = _call_helper(
            model.residual_callable,
            ((a, b, c, omega), (a, b, c), (a, b), ({"a": a, "b": b, "c": c, "omega": omega},)),
        )

    lambda_payload = None
    if model.lambda_callable is not None:
        lambda_payload = _call_helper(
            model.lambda_callable,
            ((a, b, c, omega), (a, b, c), (a, b), ({"a": a, "b": b, "c": c, "omega": omega},)),
        )

    residual = _value_from_payload(
        payload,
        ("residual", "zero_mode_residual", "min_residual", "r"),
    )
    lambda_value = _value_from_payload(
        payload,
        ("lambda", "lambda_value", "leakage_lambda", "triadic_lambda"),
    )
    if lambda_value is None:
        lambda_value = _value_from_payload(
            lambda_payload,
            ("lambda", "lambda_value", "leakage_lambda", "triadic_lambda"),
        )
    if lambda_value is None:
        lambda_value = _as_finite_float(lambda_payload)

    if residual is None and lambda_value is not None and lambda_value >= 0.0:
        residual = math.sqrt(lambda_value)
    if residual is None:
        residual = _as_finite_float(payload)
    if residual is None:
        return AngularResidualPayload(float("inf"), "residual-missing", c, True, lambda_value)

    family = _string_from_payload(
        payload,
        ("family", "zero_mode_family", "hit_family", "branch"),
    ) or "angular"
    return AngularResidualPayload(residual, family, c, False, lambda_value)


def output_omega(
    a: Vec3,
    b: Vec3,
    c: Vec3,
    model: FrameModel,
    pole_cutoff: float,
) -> Optional[Vec3]:
    if model.name == "tangent-proxy":
        return tangent_frame_omega(c, pole_cutoff=pole_cutoff)
    if model.name == "exact-strain":
        return exact_strain_omega(a, b, c, model)
    return None


def fibonacci_sphere(n: int) -> List[Vec3]:
    if n <= 0:
        return []
    points: List[Vec3] = []
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    for k in range(n):
        z = 1.0 - (2.0 * (k + 0.5) / n)
        radius = math.sqrt(max(1.0 - z * z, 0.0))
        theta = golden_angle * k
        points.append((math.cos(theta) * radius, math.sin(theta) * radius, z))
    return points


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(1.0 - z * z, 0.0))
    return (math.cos(theta) * r, math.sin(theta) * r, z)


@dataclass(frozen=True)
class Residual:
    residual: float
    family: str
    c: Vec3
    omega_missing: bool
    lambda_value: Optional[float] = None


@dataclass(frozen=True)
class Candidate:
    a: Vec3
    b: Vec3
    c: Vec3
    residual: float
    family: str
    best_next_residual: float
    best_next_family: str
    second_generation_survives: bool
    lambda_value: Optional[float] = None
    best_next_lambda_value: Optional[float] = None


def zero_mode_residual(
    a: Vec3,
    b: Vec3,
    model: FrameModel,
    pole_cutoff: float,
) -> Optional[Residual]:
    c = normalize(add(a, b))
    if c is None:
        return None
    if model.name == "s2-biot-savart":
        angular = s2_biot_savart_residual(a, b, model)
        return Residual(
            angular.residual,
            angular.family,
            angular.c,
            angular.omega_missing,
            angular.lambda_value,
        )
    omega = output_omega(a, b, c, model, pole_cutoff=pole_cutoff)
    if omega is None:
        return Residual(float("inf"), "omega-missing", c, True)

    pc_a = project_tangent(c, a)
    pc_b = project_tangent(c, b)
    n_a = norm(pc_a)
    n_b = norm(pc_b)

    family_i = float("inf")
    if n_b > EPS:
        b_hat = scale(1.0 / n_b, pc_b)
        # Parallel or antiparallel: sin(angle) = ||omega x b_hat||.
        family_i = norm(cross(omega, b_hat))

    family_ii = float("inf")
    if n_a > EPS:
        a_hat = scale(1.0 / n_a, pc_a)
        # Orthogonality residual.
        family_ii = abs(dot(omega, a_hat))

    if family_i <= family_ii:
        return Residual(family_i, "I", c, False)
    return Residual(family_ii, "II", c, False)


def quantiles(values: Sequence[float]) -> dict:
    finite = sorted(x for x in values if math.isfinite(x))
    if not finite:
        return {"count": 0}
    qs = {}
    for label, q in [
        ("min", 0.0),
        ("p05", 0.05),
        ("p25", 0.25),
        ("median", 0.5),
        ("p75", 0.75),
        ("p95", 0.95),
        ("max", 1.0),
    ]:
        idx = min(len(finite) - 1, max(0, int(round(q * (len(finite) - 1)))))
        qs[label] = finite[idx]
    qs["mean"] = statistics.fmean(finite)
    qs["count"] = len(finite)
    return qs


def estimate_output_width(outputs: Sequence[Vec3], normals: Sequence[Vec3]) -> dict:
    if not outputs or not normals:
        return {
            "estimated_width": None,
            "best_normal": None,
            "hit_fraction_eta": {},
        }

    best_width = -1.0
    best_normal = normals[0]
    min_abs_values = []
    for n in normals:
        m = min(abs(dot(n, c)) for c in outputs)
        min_abs_values.append(m)
        if m > best_width:
            best_width = m
            best_normal = n

    hit_fraction_eta = {}
    for eta in (0.01, 0.025, 0.05, 0.1, 0.2):
        hits = sum(1 for m in min_abs_values if m <= eta)
        hit_fraction_eta[str(eta)] = hits / len(min_abs_values)

    return {
        "estimated_width": best_width,
        "best_normal": best_normal,
        "normal_min_abs_dot_quantiles": quantiles(min_abs_values),
        "hit_fraction_eta": hit_fraction_eta,
    }


def run_probe(args: argparse.Namespace) -> dict:
    rng = random.Random(args.seed)
    frame_model = make_frame_model(args.frame_model)
    continuation_pool = fibonacci_sphere(args.continuations)
    normal_pool = fibonacci_sphere(args.normals)

    candidates: List[Candidate] = []
    single_residuals: List[float] = []
    single_lambdas: List[float] = []
    best_next_residuals: List[float] = []
    best_next_lambdas: List[float] = []
    omega_missing = 0
    antipodal_skips = 0

    for _ in range(args.pairs):
        a = random_unit(rng)
        b = random_unit(rng)
        res = zero_mode_residual(a, b, frame_model, args.pole_cutoff)
        if res is None:
            antipodal_skips += 1
            continue
        if res.omega_missing:
            omega_missing += 1
            continue
        single_residuals.append(res.residual)
        if res.lambda_value is not None:
            single_lambdas.append(res.lambda_value)
        if res.residual > args.zero_threshold:
            continue

        best_next = float("inf")
        best_next_family = "none"
        best_next_lambda: Optional[float] = None
        for d in continuation_pool:
            nxt = zero_mode_residual(res.c, d, frame_model, args.pole_cutoff)
            if nxt is None or nxt.omega_missing:
                continue
            if nxt.residual < best_next:
                best_next = nxt.residual
                best_next_family = nxt.family
                best_next_lambda = nxt.lambda_value

        best_next_residuals.append(best_next)
        if best_next_lambda is not None:
            best_next_lambdas.append(best_next_lambda)
        candidates.append(
            Candidate(
                a=a,
                b=b,
                c=res.c,
                residual=res.residual,
                family=res.family,
                best_next_residual=best_next,
                best_next_family=best_next_family,
                second_generation_survives=best_next <= args.depth2_threshold,
                lambda_value=res.lambda_value,
                best_next_lambda_value=best_next_lambda,
            )
        )

    single_outputs = [x.c for x in candidates]
    surviving_outputs = [x.c for x in candidates if x.second_generation_survives]
    family_counts = {"I": 0, "II": 0}
    next_family_counts = {"I": 0, "II": 0, "none": 0}
    for cnd in candidates:
        family_counts[cnd.family] = family_counts.get(cnd.family, 0) + 1
        next_family_counts[cnd.best_next_family] = (
            next_family_counts.get(cnd.best_next_family, 0) + 1
        )

    top_candidates = sorted(
        candidates, key=lambda x: (x.second_generation_survives is False, x.best_next_residual)
    )[: args.show]

    return {
        "warning": (
            "finite sampled falsification probe only; exact-strain and "
            "s2-biot-savart are diagnostic helper-backed models, not proof"
        ),
        "frame_model": {
            "name": frame_model.name,
            "exact_symbol_available": frame_model.exact_symbol_available,
            "exact_symbol_source": frame_model.exact_symbol_source,
            "caveats": list(frame_model.caveats),
        },
        "parameters": {
            "seed": args.seed,
            "pairs": args.pairs,
            "continuations": args.continuations,
            "normals": args.normals,
            "frame_model": args.frame_model,
            "zero_threshold": args.zero_threshold,
            "depth2_threshold": args.depth2_threshold,
            "pole_cutoff": args.pole_cutoff,
        },
        "threshold_metadata": {
            "single_depth_threshold_name": "zero_threshold",
            "single_depth_threshold_value": args.zero_threshold,
            "depth2_threshold_name": "depth2_threshold",
            "depth2_threshold_value": args.depth2_threshold,
            "threshold_quantity": (
                "helper residual for s2-biot-savart; sqrt(helper lambda) only "
                "when the helper supplies lambda without residual"
                if frame_model.name == "s2-biot-savart"
                else "zero-mode residual"
            ),
            "lambda_quantity": (
                "helper lambda from scripts/ns_s2_biot_savart_eigenbundle.py"
                if frame_model.name == "s2-biot-savart"
                else "not reported by this frame model"
            ),
        },
        "counts": {
            "sampled_pairs": args.pairs,
            "antipodal_skips": antipodal_skips,
            "omega_missing": omega_missing,
            "single_depth_zeroish": len(candidates),
            "depth2_survivors": len(surviving_outputs),
            "depth2_survival_fraction_of_zeroish": (
                len(surviving_outputs) / len(candidates) if candidates else 0.0
            ),
            "single_family_counts": family_counts,
            "best_next_family_counts": next_family_counts,
        },
        "single_residual_quantiles": quantiles(single_residuals),
        "single_lambda_quantiles": quantiles(single_lambdas),
        "best_next_residual_quantiles_for_zeroish": quantiles(best_next_residuals),
        "best_next_lambda_quantiles_for_zeroish": quantiles(best_next_lambdas),
        "angular_model_depth2_survival_counts": (
            {
                "single_depth_zeroish": len(candidates),
                "depth2_survivors": len(surviving_outputs),
                "depth2_failures": len(candidates) - len(surviving_outputs),
                "depth2_survival_fraction_of_zeroish": (
                    len(surviving_outputs) / len(candidates) if candidates else 0.0
                ),
                "zero_threshold": args.zero_threshold,
                "depth2_threshold": args.depth2_threshold,
            }
            if frame_model.name == "s2-biot-savart"
            else None
        ),
        "single_depth_output_width_estimate": estimate_output_width(
            single_outputs, normal_pool
        ),
        "depth2_survivor_output_width_estimate": estimate_output_width(
            surviving_outputs, normal_pool
        ),
        "top_depth2_candidates": [
            {
                "c": cnd.c,
                "single_residual": cnd.residual,
                "single_family": cnd.family,
                "best_next_residual": cnd.best_next_residual,
                "best_next_family": cnd.best_next_family,
                "lambda": cnd.lambda_value,
                "best_next_lambda": cnd.best_next_lambda_value,
                "survives": cnd.second_generation_survives,
            }
            for cnd in top_candidates
        ],
    }


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Sample finite NS triadic depth-2 cascade closure residuals."
    )
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--pairs", type=int, default=8000)
    parser.add_argument("--continuations", type=int, default=160)
    parser.add_argument("--normals", type=int, default=512)
    parser.add_argument(
        "--frame-model",
        choices=("tangent-proxy", "exact-strain", "s2-biot-savart", "angular-biot-savart"),
        default="tangent-proxy",
        help=(
            "Output omega model: tangent-proxy keeps the historical generic "
            "frame; exact-strain uses scripts/ns_exact_strain_eigenbundle.py "
            "when present; s2-biot-savart/angular-biot-savart uses "
            "scripts/ns_s2_biot_savart_eigenbundle.py angular omega_hat(c) "
            "and helper residual/lambda. Helper-backed modes fail closed when "
            "their helper/API is unavailable."
        ),
    )
    parser.add_argument("--zero-threshold", type=float, default=0.015)
    parser.add_argument("--depth2-threshold", type=float, default=0.015)
    parser.add_argument("--pole-cutoff", type=float, default=1.0e-5)
    parser.add_argument("--show", type=int, default=8)
    parser.add_argument("--json", action="store_true", help="Emit only JSON.")
    args = parser.parse_args(argv)

    report = run_probe(args)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0

    print("NS cascade depth-2 finite falsification probe")
    print("WARNING:", report["warning"])
    print()
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
