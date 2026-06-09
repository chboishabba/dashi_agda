#!/usr/bin/env python3
"""Numerical harness for true-Leray equal-scale triadic output-width targets.

This is an exploratory finite-dimensional sampler, not a proof certificate.
It samples equal-scale triads

    a, b in S^2,    c = (a + b) / |a + b|,

computes tangential projections at the output direction c, evaluates the
single-depth zero-mode residual families recorded in the DASHI triadic NS
boundary receipts, and estimates how much of S^2 is covered by the output
projection of near-zero triads.

The vorticity/stretching frame is configurable because this harness is meant
to falsify or stress-test candidate output-width mechanisms before any theorem
promotion.  The implemented frame models are synthetic tangent-frame models;
they are not a substitute for the exact Biot-Savart strain eigenbundle.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import random
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable, Sequence


Vec3 = tuple[float, float, float]

EPS = 1.0e-12
SCRIPT_DIR = Path(__file__).resolve().parent
EXACT_PROVIDER_PATH = SCRIPT_DIR / "ns_exact_strain_eigenbundle.py"
S2_BIOT_SAVART_PROVIDER_PATH = SCRIPT_DIR / "ns_s2_biot_savart_eigenbundle.py"


@dataclass(frozen=True)
class ResidualRecord:
    family_i: float
    family_ii: float
    min_residual: float
    hit_family: str


@dataclass(frozen=True)
class RunSummary:
    seed: int
    samples_requested: int
    triads_accepted: int
    anti_parallel_rejects: int
    tolerance: float
    frame_model: str
    frame_source: str
    frame_axis: Vec3
    frame_twist: float
    exact_polarization_model: str | None
    exact_polarization_seed: int | None
    exact_degenerate_outputs: int
    zero_hits_single_depth: int
    family_i_hits: int
    family_ii_hits: int
    both_family_hits: int
    hit_fraction_single_depth: float
    min_single_residual: float
    median_single_residual: float
    p95_single_residual: float
    lambda_quantiles: dict[str, float]
    near_zero_count_at_tolerance: int
    output_bin_count_all: int
    output_bin_count_zero: int
    output_bin_coverage_all: float
    output_bin_coverage_zero: float
    candidate_normals: int
    estimated_width_zero_outputs: float | None
    estimated_width_witness_normal: Vec3 | None
    estimated_width_all_outputs: float | None
    depth2_trials_per_hit: int
    depth2_continuation_hits: int | None
    depth2_hit_fraction_among_single_hits: float | None
    notes: list[str]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--samples", type=int, default=20000)
    parser.add_argument("--tolerance", type=float, default=1.0e-3)
    parser.add_argument(
        "--frame-model",
        choices=("fixed-axis", "azimuthal", "mobius", "exact-strain", "s2-biot-savart"),
        default="mobius",
        help=(
            "Output frame model. fixed-axis, azimuthal, and mobius are synthetic "
            "tangent proxies; exact-strain uses scripts/ns_exact_strain_eigenbundle.py "
            "when present, otherwise a local true-Leray finite-symbol fallback; "
            "s2-biot-savart uses scripts/ns_s2_biot_savart_eigenbundle.py when "
            "present, otherwise the local angular m11/m12 formula."
        ),
    )
    parser.add_argument("--axis", nargs=3, type=float, default=(0.0, 0.0, 1.0))
    parser.add_argument("--frame-twist", type=float, default=1.0)
    parser.add_argument(
        "--exact-polarization-model",
        choices=("canonical", "seeded", "helical-plus", "helical-minus"),
        default="canonical",
        help=(
            "Input divergence-free polarization rule for --frame-model exact-strain. "
            "helical-* are real two-frame stand-ins used only by this finite symbol."
        ),
    )
    parser.add_argument(
        "--exact-polarization-seed",
        type=int,
        default=None,
        help="Seed for the exact-strain seeded input-polarization rule.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Accepted for explicitness; JSON is the default output format.",
    )
    parser.add_argument("--bins", type=int, default=512, help="Fibonacci sphere bins for output coverage.")
    parser.add_argument("--normals", type=int, default=512, help="Candidate normals for width scan.")
    parser.add_argument(
        "--depth2-trials-per-hit",
        type=int,
        default=0,
        help="For each single-depth zero hit, sample this many d directions and test (c,d,e).",
    )
    parser.add_argument(
        "--csv",
        action="store_true",
        help="Also print a compact csv-ish key,value summary after JSON.",
    )
    return parser.parse_args()


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


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, dot(u, u)))


def normalize(u: Vec3) -> Vec3 | None:
    n = norm(u)
    if n <= EPS:
        return None
    return (u[0] / n, u[1] / n, u[2] / n)


def project_tangent(c: Vec3, v: Vec3) -> Vec3:
    return add(v, scale(-dot(v, c), c))


def fallback_axis(c: Vec3, axis: Vec3) -> Vec3:
    candidates = (axis, (1.0, 0.0, 0.0), (0.0, 1.0, 0.0), (0.0, 0.0, 1.0))
    best = candidates[0]
    best_norm = -1.0
    for candidate in candidates:
        tangent_norm = norm(project_tangent(c, candidate))
        if tangent_norm > best_norm:
            best_norm = tangent_norm
            best = candidate
    return best


def tangent_basis(c: Vec3, axis: Vec3) -> tuple[Vec3, Vec3]:
    e1 = normalize(project_tangent(c, fallback_axis(c, axis)))
    if e1 is None:
        raise RuntimeError("failed to construct tangent basis")
    e2 = normalize(cross(c, e1))
    if e2 is None:
        raise RuntimeError("failed to construct tangent basis")
    return e1, e2


def deterministic_seed_vector(direction: Vec3, seed: int) -> Vec3:
    """Return a deterministic nonzero vector for seeded finite polarizations."""
    x = (
        12.9898 * direction[0]
        + 78.233 * direction[1]
        + 37.719 * direction[2]
        + 0.001 * seed
    )
    return (
        math.sin(x + 0.173 * seed),
        math.sin(1.917 * x + 0.319 * seed + 0.7),
        math.sin(2.413 * x + 0.571 * seed + 1.3),
    )


def exact_input_polarization(
    direction: Vec3,
    axis: Vec3,
    model: str,
    seed: int,
    salt: int,
) -> Vec3 | None:
    e1, e2 = tangent_basis(direction, axis)
    if model == "canonical":
        return e1
    if model == "helical-plus":
        return normalize(add(e1, e2))
    if model == "helical-minus":
        return normalize(add(e1, scale(-1.0, e2)))
    if model == "seeded":
        return normalize(project_tangent(direction, deterministic_seed_vector(direction, seed + salt)))
    raise ValueError(f"unknown exact polarization model: {model}")


def true_leray_symmetric_output(
    a: Vec3,
    b: Vec3,
    c: Vec3,
    u_a: Vec3,
    u_b: Vec3,
) -> Vec3:
    """Real finite stand-in for the exact equal-scale NS bilinear output.

    Up to harmless constants and the complex phase, the symmetrized Fourier
    symbol contributes

        P_c [ (b.u_a) u_b + (a.u_b) u_a ].

    This is a finite symbol diagnostic, not a PDE sign or regularity proof.
    """
    raw = add(scale(dot(b, u_a), u_b), scale(dot(a, u_b), u_a))
    return project_tangent(c, raw)


def local_exact_strain_frame(
    a: Vec3,
    b: Vec3,
    c: Vec3,
    axis: Vec3,
    polarization_model: str,
    polarization_seed: int,
) -> tuple[Vec3, Vec3] | None:
    u_a = exact_input_polarization(a, axis, polarization_model, polarization_seed, 101)
    u_b = exact_input_polarization(b, axis, polarization_model, polarization_seed, 211)
    if u_a is None or u_b is None:
        return None

    output_velocity = normalize(true_leray_symmetric_output(a, b, c, u_a, u_b))
    if output_velocity is None:
        return None

    # The symmetric strain symbol 1/2(c otimes v + v otimes c), with v tangent
    # to c, has top eigenvector parallel to c + v.
    e_plus = normalize(add(c, output_velocity))
    if e_plus is None:
        return None
    omega = normalize(cross(c, e_plus))
    if omega is None:
        return None
    return e_plus, omega


def load_provider(path: Path, module_name: str) -> ModuleType | None:
    if not path.exists():
        return None
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not load provider at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def load_exact_provider() -> ModuleType | None:
    return load_provider(EXACT_PROVIDER_PATH, "ns_exact_strain_eigenbundle")


def load_s2_biot_savart_provider() -> ModuleType | None:
    return load_provider(S2_BIOT_SAVART_PROVIDER_PATH, "ns_s2_biot_savart_eigenbundle")


def coerce_vec3(value: Any) -> Vec3 | None:
    if isinstance(value, (list, tuple)) and len(value) == 3:
        try:
            return (float(value[0]), float(value[1]), float(value[2]))
        except (TypeError, ValueError):
            return None
    return None


def call_exact_provider(
    provider: ModuleType,
    a: Vec3,
    b: Vec3,
    c: Vec3,
    axis: Vec3,
    polarization_model: str,
    polarization_seed: int,
) -> tuple[Vec3, Vec3] | None:
    if hasattr(provider, "triadic_strain_eigenbundle_from_models"):
        model_map = {
            "canonical": ("e1", "e2", 0.0, 0.0),
            "helical-plus": ("plus45", "plus45", 0.0, 0.0),
            "helical-minus": ("minus45", "minus45", 0.0, 0.0),
            "seeded": (
                "angle",
                "angle",
                math.sin(0.017 * polarization_seed + dot(a, axis)) * math.pi,
                math.sin(0.019 * polarization_seed + dot(b, axis) + 0.5) * math.pi,
            ),
        }
        model_a, model_b, angle_a, angle_b = model_map[polarization_model]
        bundle = provider.triadic_strain_eigenbundle_from_models(
            a,
            b,
            model_a=model_a,
            model_b=model_b,
            angle_a=angle_a,
            angle_b=angle_b,
            symmetrized=True,
        )
        if bundle is None:
            return None
        strain = getattr(bundle, "strain", None)
        if strain is None:
            return None
        e_plus = coerce_vec3(getattr(strain, "e_plus", None))
        omega = coerce_vec3(getattr(strain, "omega_out", None))
        if e_plus is None or omega is None:
            return None
        return e_plus, omega

    function_names = (
        "output_frame",
        "exact_output_frame",
        "strain_frame",
        "frame_for_triad",
        "compute_frame",
    )
    frame_fn = next((getattr(provider, name, None) for name in function_names if hasattr(provider, name)), None)
    if frame_fn is None:
        raise RuntimeError(
            "scripts/ns_exact_strain_eigenbundle.py is present but exports none of: "
            + ", ".join(function_names)
        )

    try:
        result = frame_fn(
            a=a,
            b=b,
            c=c,
            axis=axis,
            polarization_model=polarization_model,
            polarization_seed=polarization_seed,
        )
    except TypeError:
        try:
            result = frame_fn(a, b, c, axis)
        except TypeError:
            result = frame_fn(a, b, c)

    if result is None:
        return None
    if isinstance(result, dict):
        e_plus = coerce_vec3(result.get("e_plus") or result.get("stretching") or result.get("strain"))
        omega = coerce_vec3(result.get("omega") or result.get("vorticity"))
    elif isinstance(result, (list, tuple)) and len(result) >= 2:
        e_plus = coerce_vec3(result[0])
        omega = coerce_vec3(result[1])
    else:
        raise RuntimeError("exact provider returned an unsupported frame shape")

    if e_plus is None:
        return None
    if omega is None:
        omega = normalize(cross(c, e_plus))
    if omega is None:
        return None
    e_plus = normalize(e_plus)
    omega = normalize(project_tangent(c, omega))
    if e_plus is None or omega is None:
        return None
    return e_plus, omega


def local_s2_biot_savart_frame(c: Vec3) -> tuple[Vec3, Vec3] | None:
    """Return the S2 angular Biot-Savart strain frame at output direction c.

    This is the finite angular formula requested for the exact S2 diagnostic:

        m11 = 1/2 (cos^2 psi - sin^2 psi cos 2phi)
        m12 = -1/2 sin^2 psi sin 2phi

    The output vorticity direction is omega_hat(c)=c x e_+(c).  It depends
    only on c and is not built tautologically from the triadic output Y.
    """

    c_hat = normalize(c)
    if c_hat is None:
        return None

    x, y, z = c_hat
    phi = math.atan2(y, x)
    sin_psi = math.sqrt(max(0.0, 1.0 - z * z))
    cos_psi = z

    e_psi = (
        cos_psi * math.cos(phi),
        cos_psi * math.sin(phi),
        -sin_psi,
    )
    e_phi = (-math.sin(phi), math.cos(phi), 0.0)

    # At the poles phi is a gauge choice; the line-field formula remains
    # fail-closed and deterministic for harness diagnostics.
    m11 = 0.5 * (cos_psi * cos_psi - sin_psi * sin_psi * math.cos(2.0 * phi))
    m12 = -0.5 * sin_psi * sin_psi * math.sin(2.0 * phi)
    beta = 0.5 * math.atan2(m12, m11)

    e_plus = normalize(add(scale(math.cos(beta), e_psi), scale(math.sin(beta), e_phi)))
    if e_plus is None:
        return None
    e_plus = normalize(project_tangent(c_hat, e_plus))
    if e_plus is None:
        return None
    omega = normalize(cross(c_hat, e_plus))
    if omega is None:
        return None
    return e_plus, omega


def call_s2_biot_savart_provider(provider: ModuleType, c: Vec3) -> tuple[Vec3, Vec3] | None:
    function_names = (
        "s2_biot_savart_frame",
        "biot_savart_frame",
        "angular_frame",
        "frame",
        "angular_eigenbundle",
        "angular_eigenbundle_at",
        "omega_hat",
        "s2_biot_savart_omega_hat",
        "biot_savart_omega_hat",
    )
    frame_fn = next((getattr(provider, name, None) for name in function_names if hasattr(provider, name)), None)
    if frame_fn is None:
        raise RuntimeError(
            "scripts/ns_s2_biot_savart_eigenbundle.py is present but exports none of: "
            + ", ".join(function_names)
        )

    try:
        result = frame_fn(c=c)
    except TypeError:
        result = frame_fn(c)

    e_plus: Vec3 | None = None
    omega: Vec3 | None = None
    if hasattr(result, "omega_hat") or hasattr(result, "e_plus"):
        e_plus = coerce_vec3(getattr(result, "e_plus", None))
        omega = coerce_vec3(getattr(result, "omega_hat", None) or getattr(result, "omega", None))
    elif isinstance(result, dict):
        e_plus = coerce_vec3(result.get("e_plus") or result.get("stretching") or result.get("strain"))
        omega = coerce_vec3(result.get("omega_hat") or result.get("omega") or result.get("vorticity"))
    elif isinstance(result, (list, tuple)) and len(result) == 3 and all(isinstance(x, (int, float)) for x in result):
        omega = coerce_vec3(result)
    elif isinstance(result, (list, tuple)) and len(result) >= 2:
        e_plus = coerce_vec3(result[0])
        omega = coerce_vec3(result[1])
    else:
        raise RuntimeError("S2 Biot-Savart provider returned an unsupported frame shape")

    c_hat = normalize(c)
    if c_hat is None:
        return None
    if omega is not None:
        omega = normalize(project_tangent(c_hat, omega))
    if e_plus is not None:
        e_plus = normalize(project_tangent(c_hat, e_plus))
    if omega is None and e_plus is not None:
        omega = normalize(cross(c_hat, e_plus))
    if e_plus is None and omega is not None:
        e_plus = normalize(cross(omega, c_hat))
    if e_plus is None or omega is None:
        return None
    return e_plus, omega


@dataclass
class FrameContext:
    model: str
    axis: Vec3
    twist: float
    exact_polarization_model: str
    exact_polarization_seed: int
    exact_provider: ModuleType | None
    s2_biot_savart_provider: ModuleType | None
    exact_degenerate_outputs: int = 0

    @property
    def frame_source(self) -> str:
        if self.model == "s2-biot-savart":
            if self.s2_biot_savart_provider is not None:
                return f"external:{S2_BIOT_SAVART_PROVIDER_PATH.name}"
            return "local-s2-biot-savart-angular-formula"
        if self.model != "exact-strain":
            return "synthetic-proxy"
        if self.exact_provider is not None:
            return f"external:{EXACT_PROVIDER_PATH.name}"
        return "local-true-leray-finite-symbol"

    def frame(self, a: Vec3, b: Vec3, c: Vec3) -> tuple[Vec3, Vec3] | None:
        if self.model == "s2-biot-savart":
            if self.s2_biot_savart_provider is not None:
                frame = call_s2_biot_savart_provider(self.s2_biot_savart_provider, c)
            else:
                frame = local_s2_biot_savart_frame(c)
            if frame is None:
                self.exact_degenerate_outputs += 1
            return frame
        if self.model == "exact-strain":
            if self.exact_provider is not None:
                frame = call_exact_provider(
                    self.exact_provider,
                    a,
                    b,
                    c,
                    self.axis,
                    self.exact_polarization_model,
                    self.exact_polarization_seed,
                )
            else:
                frame = local_exact_strain_frame(
                    a,
                    b,
                    c,
                    self.axis,
                    self.exact_polarization_model,
                    self.exact_polarization_seed,
                )
            if frame is None:
                self.exact_degenerate_outputs += 1
            return frame
        return output_frame(c, self.axis, self.model, self.twist)


def output_frame(c: Vec3, axis: Vec3, model: str, twist: float) -> tuple[Vec3, Vec3]:
    """Return synthetic (stretching, vorticity) unit tangent frame at c."""
    if model == "fixed-axis":
        e_plus = normalize(project_tangent(c, fallback_axis(c, axis)))
    elif model == "azimuthal":
        e_plus = normalize(cross(fallback_axis(c, axis), c))
    elif model == "mobius":
        e1, e2 = tangent_basis(c, axis)
        longitude = math.atan2(dot(cross(axis, c), e2), dot(c, axis))
        angle = 0.5 * twist * longitude
        e_plus = normalize(add(scale(math.cos(angle), e1), scale(math.sin(angle), e2)))
    else:
        raise ValueError(f"unknown frame model: {model}")

    if e_plus is None:
        e_plus, _ = tangent_basis(c, axis)
    omega = normalize(cross(c, e_plus))
    if omega is None:
        raise RuntimeError("failed to construct vorticity direction")
    return e_plus, omega


def random_unit(rng: random.Random) -> Vec3:
    z = rng.uniform(-1.0, 1.0)
    theta = rng.uniform(0.0, 2.0 * math.pi)
    r = math.sqrt(max(0.0, 1.0 - z * z))
    return (r * math.cos(theta), r * math.sin(theta), z)


def fibonacci_sphere(count: int) -> list[Vec3]:
    if count <= 0:
        raise ValueError("count must be positive")
    golden_angle = math.pi * (3.0 - math.sqrt(5.0))
    points: list[Vec3] = []
    for i in range(count):
        z = 1.0 - (2.0 * (i + 0.5) / count)
        r = math.sqrt(max(0.0, 1.0 - z * z))
        theta = golden_angle * i
        points.append((r * math.cos(theta), r * math.sin(theta), z))
    return points


def nearest_bin_index(v: Vec3, bins: Sequence[Vec3]) -> int:
    best_index = 0
    best_dot = -2.0
    for index, point in enumerate(bins):
        value = dot(v, point)
        if value > best_dot:
            best_dot = value
            best_index = index
    return best_index


def triad_output(a: Vec3, b: Vec3) -> Vec3 | None:
    return normalize(add(a, b))


def parallel_residual(u: Vec3, v: Vec3) -> float:
    nu = norm(u)
    nv = norm(v)
    if nu <= EPS or nv <= EPS:
        return 1.0
    return norm(cross(u, v)) / (nu * nv)


def corrected_s2_lambda_residual(a: Vec3, b: Vec3, c: Vec3, omega: Vec3) -> float:
    pc_b = project_tangent(c, b)
    pc_b_norm_sq = dot(pc_b, pc_b)
    if pc_b_norm_sq <= EPS * EPS:
        return 1.0
    omega_hat = normalize(project_tangent(c, omega))
    a_hat = normalize(a)
    if omega_hat is None or a_hat is None:
        return 1.0
    off_omega = add(pc_b, scale(-dot(pc_b, omega_hat), omega_hat))
    leakage_ratio = dot(off_omega, off_omega) / pc_b_norm_sq
    alignment_factor = dot(a_hat, omega_hat) ** 2
    return max(0.0, min(1.0, leakage_ratio * alignment_factor))


def residuals_for_triad(a: Vec3, b: Vec3, c: Vec3, frame_context: FrameContext) -> ResidualRecord | None:
    frame = frame_context.frame(a, b, c)
    if frame is None:
        return None
    _, omega = frame
    pc_b = project_tangent(c, b)
    pc_a = project_tangent(c, a)

    if frame_context.model == "s2-biot-savart":
        omega_hat = normalize(project_tangent(c, omega))
        if omega_hat is None:
            return None
        lambda_residual = corrected_s2_lambda_residual(a, b, c, omega_hat)
        family_i = parallel_residual(omega_hat, pc_b)
        pc_a_norm = norm(pc_a)
        family_ii = abs(dot(omega_hat, pc_a)) / pc_a_norm if pc_a_norm > EPS else 1.0
        if family_i <= 1.0e-15 and family_ii <= 1.0e-15:
            hit_family = "both"
        elif family_i <= 1.0e-15:
            hit_family = "family_i"
        elif family_ii <= 1.0e-15:
            hit_family = "family_ii"
        else:
            hit_family = "lambda"
        return ResidualRecord(
            family_i=family_i,
            family_ii=family_ii,
            min_residual=lambda_residual,
            hit_family=hit_family,
        )

    # Family I: omega(c) parallel P_c(b).
    family_i = parallel_residual(omega, pc_b)

    # Family II: omega(c) perpendicular P_c(a), equivalently omega dot a = 0.
    pc_a_norm = norm(pc_a)
    family_ii = abs(dot(omega, pc_a)) / pc_a_norm if pc_a_norm > EPS else 1.0

    min_res = min(family_i, family_ii)
    if abs(family_i - family_ii) <= 1.0e-15:
        hit_family = "both"
    elif family_i < family_ii:
        hit_family = "family_i"
    else:
        hit_family = "family_ii"
    return ResidualRecord(family_i=family_i, family_ii=family_ii, min_residual=min_res, hit_family=hit_family)


def quantile(values: Sequence[float], q: float) -> float:
    if not values:
        return math.nan
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[index]


def quantile_map(values: Sequence[float]) -> dict[str, float]:
    return {
        "min": min(values) if values else math.nan,
        "q01": quantile(values, 0.01),
        "q05": quantile(values, 0.05),
        "q25": quantile(values, 0.25),
        "q50": quantile(values, 0.50),
        "q75": quantile(values, 0.75),
        "q95": quantile(values, 0.95),
        "q99": quantile(values, 0.99),
        "max": max(values) if values else math.nan,
    }


def estimate_width(outputs: Sequence[Vec3], normals: Sequence[Vec3]) -> tuple[float | None, Vec3 | None]:
    """Estimate sup_n inf_c |n.c| over sampled output set."""
    if not outputs:
        return None, None
    best_width = -1.0
    best_normal: Vec3 | None = None
    for n in normals:
        min_abs = min(abs(dot(n, c)) for c in outputs)
        if min_abs > best_width:
            best_width = min_abs
            best_normal = n
    return best_width, best_normal


def run_depth2_probe(
    rng: random.Random,
    zero_outputs: Sequence[Vec3],
    frame_context: FrameContext,
    tolerance: float,
    trials_per_hit: int,
) -> int | None:
    if trials_per_hit <= 0:
        return None
    continuations = 0
    for c in zero_outputs:
        for _ in range(trials_per_hit):
            d = random_unit(rng)
            e = triad_output(c, d)
            if e is None:
                continue
            rec = residuals_for_triad(c, d, e, frame_context)
            if rec is None:
                continue
            if rec.min_residual <= tolerance:
                continuations += 1
                break
    return continuations


def fmt_vec(v: Vec3 | None) -> list[float] | None:
    if v is None:
        return None
    return [round(v[0], 8), round(v[1], 8), round(v[2], 8)]


def build_summary(args: argparse.Namespace) -> RunSummary:
    rng = random.Random(args.seed)
    axis = normalize(tuple(args.axis))  # type: ignore[arg-type]
    if axis is None:
        raise ValueError("--axis must be nonzero")
    exact_seed = args.exact_polarization_seed if args.exact_polarization_seed is not None else args.seed + 1701
    frame_context = FrameContext(
        model=args.frame_model,
        axis=axis,
        twist=args.frame_twist,
        exact_polarization_model=args.exact_polarization_model,
        exact_polarization_seed=exact_seed,
        exact_provider=load_exact_provider() if args.frame_model == "exact-strain" else None,
        s2_biot_savart_provider=(
            load_s2_biot_savart_provider() if args.frame_model == "s2-biot-savart" else None
        ),
    )

    bins = fibonacci_sphere(args.bins)
    normals = fibonacci_sphere(args.normals)
    all_output_bins: set[int] = set()
    zero_output_bins: set[int] = set()
    all_outputs: list[Vec3] = []
    zero_outputs: list[Vec3] = []
    residual_values: list[float] = []
    anti_parallel_rejects = 0
    family_i_hits = 0
    family_ii_hits = 0
    both_family_hits = 0

    for _ in range(args.samples):
        a = random_unit(rng)
        b = random_unit(rng)
        c = triad_output(a, b)
        if c is None:
            anti_parallel_rejects += 1
            continue

        all_outputs.append(c)
        all_output_bins.add(nearest_bin_index(c, bins))
        rec = residuals_for_triad(a, b, c, frame_context)
        if rec is None:
            continue
        residual_values.append(rec.min_residual)

        family_i_hit = rec.family_i <= args.tolerance
        family_ii_hit = rec.family_ii <= args.tolerance
        near_zero_hit = (
            rec.min_residual <= args.tolerance
            if args.frame_model == "s2-biot-savart"
            else family_i_hit or family_ii_hit
        )
        if family_i_hit:
            family_i_hits += 1
        if family_ii_hit:
            family_ii_hits += 1
        if family_i_hit and family_ii_hit:
            both_family_hits += 1
        if near_zero_hit:
            zero_outputs.append(c)
            zero_output_bins.add(nearest_bin_index(c, bins))

    width_zero, witness_zero = estimate_width(zero_outputs, normals)
    width_all, _ = estimate_width(all_outputs, normals)
    depth2_hits = run_depth2_probe(
        rng,
        zero_outputs,
        frame_context,
        args.tolerance,
        args.depth2_trials_per_hit,
    )
    depth2_fraction = None
    if depth2_hits is not None:
        depth2_fraction = depth2_hits / len(zero_outputs) if zero_outputs else 0.0

    notes = [
        "Exploratory numeric harness only; no proof or promotion claim.",
        "Width estimate uses sampled candidate normals and sampled zero outputs.",
    ]
    if args.frame_model == "s2-biot-savart":
        notes.append(
            "s2-biot-savart uses omega_hat(c) from an external provider when present; "
            "this run source is " + frame_context.frame_source + "."
        )
        notes.append(
            "S2 mode uses the corrected lambda residual and does not define omega from "
            "the triadic output, avoiding the tautological output-built omega failure mode."
        )
        if frame_context.exact_degenerate_outputs:
            notes.append(
                "Some S2 Biot-Savart frames degenerated and were skipped for residual tests; "
                "see exact_degenerate_outputs."
            )
    elif args.frame_model == "exact-strain":
        notes.append(
            "exact-strain uses the external ns_exact_strain_eigenbundle.py provider when present; "
            "this run source is " + frame_context.frame_source + "."
        )
        notes.append(
            "Exact mode computes an equal-scale finite NS strain symbol from divergence-free "
            "input polarizations; it is still finite-symbol evidence, not a PDE sign theorem."
        )
        if frame_context.exact_degenerate_outputs:
            notes.append(
                "Some exact-strain outputs degenerated and were skipped for residual tests; "
                "see exact_degenerate_outputs."
            )
    else:
        notes.append(
            "Frame model is a synthetic tangent-frame proxy, not the exact NS strain eigenbundle."
        )
    if not zero_outputs:
        notes.append("No near-zero outputs were found at the selected tolerance; width is vacuous for this run.")

    triads_accepted = len(all_outputs)
    return RunSummary(
        seed=args.seed,
        samples_requested=args.samples,
        triads_accepted=triads_accepted,
        anti_parallel_rejects=anti_parallel_rejects,
        tolerance=args.tolerance,
        frame_model=args.frame_model,
        frame_source=frame_context.frame_source,
        frame_axis=axis,
        frame_twist=args.frame_twist,
        exact_polarization_model=(
            args.exact_polarization_model if args.frame_model == "exact-strain" else None
        ),
        exact_polarization_seed=(exact_seed if args.frame_model == "exact-strain" else None),
        exact_degenerate_outputs=frame_context.exact_degenerate_outputs,
        zero_hits_single_depth=len(zero_outputs),
        family_i_hits=family_i_hits,
        family_ii_hits=family_ii_hits,
        both_family_hits=both_family_hits,
        hit_fraction_single_depth=(len(zero_outputs) / triads_accepted if triads_accepted else 0.0),
        min_single_residual=(min(residual_values) if residual_values else math.nan),
        median_single_residual=quantile(residual_values, 0.5),
        p95_single_residual=quantile(residual_values, 0.95),
        lambda_quantiles=quantile_map(residual_values),
        near_zero_count_at_tolerance=len(zero_outputs),
        output_bin_count_all=len(all_output_bins),
        output_bin_count_zero=len(zero_output_bins),
        output_bin_coverage_all=len(all_output_bins) / args.bins,
        output_bin_coverage_zero=len(zero_output_bins) / args.bins,
        candidate_normals=args.normals,
        estimated_width_zero_outputs=width_zero,
        estimated_width_witness_normal=witness_zero,
        estimated_width_all_outputs=width_all,
        depth2_trials_per_hit=args.depth2_trials_per_hit,
        depth2_continuation_hits=depth2_hits,
        depth2_hit_fraction_among_single_hits=depth2_fraction,
        notes=notes,
    )


def print_csvish(summary: dict[str, object]) -> None:
    scalar_keys = [
        "seed",
        "samples_requested",
        "triads_accepted",
        "tolerance",
        "frame_model",
        "frame_source",
        "exact_polarization_model",
        "exact_polarization_seed",
        "exact_degenerate_outputs",
        "zero_hits_single_depth",
        "family_i_hits",
        "family_ii_hits",
        "hit_fraction_single_depth",
        "min_single_residual",
        "median_single_residual",
        "p95_single_residual",
        "output_bin_coverage_all",
        "output_bin_coverage_zero",
        "estimated_width_zero_outputs",
        "estimated_width_all_outputs",
        "depth2_trials_per_hit",
        "depth2_continuation_hits",
        "depth2_hit_fraction_among_single_hits",
    ]
    print("key,value")
    for key in scalar_keys:
        print(f"{key},{summary.get(key)}")


def main() -> int:
    args = parse_args()
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.tolerance < 0.0:
        raise ValueError("--tolerance must be nonnegative")
    if args.bins <= 0 or args.normals <= 0:
        raise ValueError("--bins and --normals must be positive")

    summary = asdict(build_summary(args))
    summary["frame_axis"] = fmt_vec(tuple(summary["frame_axis"]))  # type: ignore[arg-type]
    summary["estimated_width_witness_normal"] = fmt_vec(
        tuple(summary["estimated_width_witness_normal"])  # type: ignore[arg-type]
        if summary["estimated_width_witness_normal"] is not None
        else None
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    if args.csv:
        print()
        print_csvish(summary)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
