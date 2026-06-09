#!/usr/bin/env python3
"""Compact A/B diagnostic for proxy versus exact-strain NS zero-mode width.

This harness is a local falsification aid only.  It compares:

* proxy: the existing synthetic tangent-frame residual from
  ns_triadic_output_width_harness.py;
* exact_strain: a finite Fourier-symbol strain tensor built from an
  incompressible equal-scale triad interaction, followed by an actual symmetric
  3x3 eigenvector extraction.

The exact-strain branch is still a finite sampled model, not a PDE theorem and
not a Clay promotion receipt.  Its purpose is to expose whether conclusions
from the synthetic proxy survive when the stretching direction is recomputed
from a concrete incompressible strain symbol.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Sequence


SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import ns_triadic_output_width_harness as width_proxy  # noqa: E402


Vec3 = tuple[float, float, float]
Mat3 = tuple[tuple[float, float, float], tuple[float, float, float], tuple[float, float, float]]

EPS = 1.0e-12


@dataclass(frozen=True)
class ModelResult:
    model: str
    zero_hits: int
    family_i_hits: int
    family_ii_hits: int
    both_family_hits: int
    estimated_width: float | None
    depth2_survival: int
    degeneracy_counts: dict[str, int]
    min_residual: float | None
    median_residual: float | None
    p95_residual: float | None


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--samples", type=int, default=1200)
    parser.add_argument("--tolerance", type=float, default=1.0e-3)
    parser.add_argument("--bins", type=int, default=256)
    parser.add_argument("--normals", type=int, default=256)
    parser.add_argument("--axis", nargs=3, type=float, default=(0.0, 0.0, 1.0))
    parser.add_argument("--frame-model", choices=("fixed-axis", "azimuthal", "mobius"), default="mobius")
    parser.add_argument("--frame-twist", type=float, default=1.0)
    parser.add_argument(
        "--exact-polarization-model",
        choices=("canonical", "seeded", "helical-plus", "helical-minus"),
        default="canonical",
    )
    parser.add_argument("--exact-polarization-seed", type=int, default=None)
    parser.add_argument("--depth2-trials-per-hit", type=int, default=2)
    parser.add_argument("--json", action="store_true", help="Emit JSON only.")
    return parser.parse_args(argv)


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def sub(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2],)


def dot(u: Vec3, v: Vec3) -> float:
    return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]


def cross(u: Vec3, v: Vec3) -> Vec3:
    return (
        u[1] * v[2] - u[2] * v[1],
        u[2] * v[0] - u[0] * v[2],
        u[0] * v[1] - u[1] * v[0],
    )


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, dot(u, u)))


def normalize(u: Vec3) -> Vec3 | None:
    n = norm(u)
    if n <= EPS:
        return None
    return (u[0] / n, u[1] / n, u[2] / n)


def project_tangent(c: Vec3, v: Vec3) -> Vec3:
    return sub(v, scale(dot(c, v), c))


def canonical_polarization(k: Vec3, axis: Vec3) -> Vec3 | None:
    raw = project_tangent(k, axis)
    if norm(raw) <= 1.0e-8:
        raw = project_tangent(k, (1.0, 0.0, 0.0))
    if norm(raw) <= 1.0e-8:
        raw = project_tangent(k, (0.0, 1.0, 0.0))
    return normalize(raw)


def triad_output(a: Vec3, b: Vec3) -> Vec3 | None:
    return normalize(add(a, b))


def mat_zero() -> list[list[float]]:
    return [[0.0, 0.0, 0.0] for _ in range(3)]


def sym_outer(u: Vec3, v: Vec3) -> Mat3:
    return tuple(
        tuple(0.5 * (u[i] * v[j] + u[j] * v[i]) for j in range(3))
        for i in range(3)
    )  # type: ignore[return-value]


def mat_vec(m: Mat3, v: Vec3) -> Vec3:
    return (
        m[0][0] * v[0] + m[0][1] * v[1] + m[0][2] * v[2],
        m[1][0] * v[0] + m[1][1] * v[1] + m[1][2] * v[2],
        m[2][0] * v[0] + m[2][1] * v[1] + m[2][2] * v[2],
    )


def rayleigh(m: Mat3, v: Vec3) -> float:
    return dot(v, mat_vec(m, v))


def eigen_residual(m: Mat3, lam: float, v: Vec3) -> float:
    mv = mat_vec(m, v)
    return norm((mv[0] - lam * v[0], mv[1] - lam * v[1], mv[2] - lam * v[2]))


def largest_eigenvector_symmetric(m: Mat3) -> tuple[float, Vec3, bool]:
    """Return a deterministic largest eigenpair for a real symmetric 3x3 matrix."""
    candidates = [
        (1.0, 0.0, 0.0),
        (0.0, 1.0, 0.0),
        (0.0, 0.0, 1.0),
        normalize((1.0, 1.0, 1.0)),
        normalize((1.0, -1.0, 1.0)),
        normalize((1.0, 1.0, -1.0)),
    ]
    vectors = [v for v in candidates if v is not None]
    best = vectors[0]
    for start in vectors:
        v = start
        for _ in range(36):
            # Shifted power iteration for symmetric matrices with possibly
            # negative eigenvalues; the shift is a Gershgorin-safe positive pad.
            radius = max(sum(abs(m[i][j]) for j in range(3)) for i in range(3)) + 1.0
            shifted = add(mat_vec(m, v), scale(radius, v))
            nxt = normalize(shifted)
            if nxt is None:
                break
            v = nxt
        if rayleigh(m, v) > rayleigh(m, best):
            best = v
    lam = rayleigh(m, best)
    degenerate = eigen_residual(m, lam, best) > 5.0e-6
    return lam, best, degenerate


def exact_strain_frame(a: Vec3, b: Vec3, c: Vec3, axis: Vec3) -> tuple[Vec3 | None, dict[str, int]]:
    counts = {
        "polarization_missing": 0,
        "nonlinear_output_zero": 0,
        "strain_norm_zero": 0,
        "eigen_solver_degenerate": 0,
    }
    ua = canonical_polarization(a, axis)
    ub_seed = canonical_polarization(b, axis)
    if ua is None or ub_seed is None:
        counts["polarization_missing"] = 1
        return None, counts

    # Give the second input a deterministic helical-style phase relative to the
    # first direction so the exact branch is not merely the same tangent proxy.
    ub_twist = normalize(cross(b, ub_seed))
    ub = normalize(add(scale(0.75, ub_seed), scale(0.25, ub_twist or ub_seed)))
    if ub is None:
        counts["polarization_missing"] = 1
        return None, counts

    raw_output_velocity = add(scale(dot(ua, b), ub), scale(dot(ub, a), ua))
    uc = normalize(project_tangent(c, raw_output_velocity))
    if uc is None:
        counts["nonlinear_output_zero"] = 1
        return None, counts

    strain = sym_outer(c, uc)
    if max(abs(strain[i][j]) for i in range(3) for j in range(3)) <= EPS:
        counts["strain_norm_zero"] = 1
        return None, counts

    _, e_plus, solver_degenerate = largest_eigenvector_symmetric(strain)
    if solver_degenerate:
        counts["eigen_solver_degenerate"] = 1
    return e_plus, counts


def residual_from_eplus(a: Vec3, b: Vec3, c: Vec3, e_plus: Vec3) -> tuple[float, float]:
    pc_a = project_tangent(c, a)
    pc_b = project_tangent(c, b)
    family_i = width_proxy.parallel_residual(e_plus, pc_b)
    n_a = norm(pc_a)
    family_ii = abs(dot(e_plus, pc_a)) / n_a if n_a > EPS else 1.0
    return family_i, family_ii


def quantile(values: Sequence[float], q: float) -> float | None:
    if not values:
        return None
    ordered = sorted(values)
    index = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[index]


def merge_counts(dst: dict[str, int], src: dict[str, int]) -> None:
    for key, value in src.items():
        dst[key] = dst.get(key, 0) + value


def run_model(
    *,
    model: str,
    triads: Sequence[tuple[Vec3, Vec3, Vec3]],
    rng: random.Random,
    axis: Vec3,
    tolerance: float,
    normals: Sequence[Vec3],
    depth2_trials_per_hit: int,
    proxy_frame_model: str,
    proxy_frame_twist: float,
    exact_polarization_model: str,
    exact_polarization_seed: int,
) -> ModelResult:
    residuals: list[float] = []
    zero_outputs: list[Vec3] = []
    family_i_hits = 0
    family_ii_hits = 0
    both_family_hits = 0
    depth2_survival = 0
    degeneracy_counts = {
        "anti_parallel_rejects": 0,
        "polarization_missing": 0,
        "nonlinear_output_zero": 0,
        "strain_norm_zero": 0,
        "eigen_solver_degenerate": 0,
        "proxy_frame_missing": 0,
    }
    frame_context = width_proxy.FrameContext(
        model=proxy_frame_model if model == "proxy" else "exact-strain",
        axis=axis,
        twist=proxy_frame_twist,
        exact_polarization_model=exact_polarization_model,
        exact_polarization_seed=exact_polarization_seed,
        exact_provider=width_proxy.load_exact_provider() if model == "exact_strain" else None,
    )

    def residual_for_triad(a: Vec3, b: Vec3, c: Vec3) -> tuple[float, float] | None:
        rec = width_proxy.residuals_for_triad(a, b, c, frame_context)
        if rec is None:
            key = "proxy_frame_missing" if model == "proxy" else "nonlinear_output_zero"
            degeneracy_counts[key] += 1
            return None
        return rec.family_i, rec.family_ii

    for a, b, c in triads:
        families = residual_for_triad(a, b, c)
        if families is None:
            continue
        family_i, family_ii = families
        residuals.append(min(family_i, family_ii))
        family_i_hit = family_i <= tolerance
        family_ii_hit = family_ii <= tolerance
        if family_i_hit:
            family_i_hits += 1
        if family_ii_hit:
            family_ii_hits += 1
        if family_i_hit and family_ii_hit:
            both_family_hits += 1
        if not (family_i_hit or family_ii_hit):
            continue
        zero_outputs.append(c)

        survived = False
        for _ in range(depth2_trials_per_hit):
            d = width_proxy.random_unit(rng)
            e = triad_output(c, d)
            if e is None:
                degeneracy_counts["anti_parallel_rejects"] += 1
                continue
            nxt = residual_for_triad(c, d, e)
            if nxt is not None and min(nxt) <= tolerance:
                survived = True
                break
        if survived:
            depth2_survival += 1

    width, _ = width_proxy.estimate_width(zero_outputs, normals)
    if model == "exact_strain":
        degeneracy_counts["exact_frame_missing_reported_by_width_proxy"] = frame_context.exact_degenerate_outputs
    return ModelResult(
        model=model,
        zero_hits=len(zero_outputs),
        family_i_hits=family_i_hits,
        family_ii_hits=family_ii_hits,
        both_family_hits=both_family_hits,
        estimated_width=width,
        depth2_survival=depth2_survival,
        degeneracy_counts=degeneracy_counts,
        min_residual=quantile(residuals, 0.0),
        median_residual=quantile(residuals, 0.5),
        p95_residual=quantile(residuals, 0.95),
    )


def build_report(args: argparse.Namespace) -> dict[str, object]:
    if args.samples <= 0:
        raise ValueError("--samples must be positive")
    if args.depth2_trials_per_hit < 0:
        raise ValueError("--depth2-trials-per-hit must be nonnegative")
    axis = normalize(tuple(args.axis))  # type: ignore[arg-type]
    if axis is None:
        raise ValueError("--axis must be nonzero")

    rng = random.Random(args.seed)
    triads: list[tuple[Vec3, Vec3, Vec3]] = []
    anti_parallel_rejects = 0
    for _ in range(args.samples):
        a = width_proxy.random_unit(rng)
        b = width_proxy.random_unit(rng)
        c = triad_output(a, b)
        if c is None:
            anti_parallel_rejects += 1
            continue
        triads.append((a, b, c))

    normals = width_proxy.fibonacci_sphere(args.normals)
    exact_seed = (
        args.exact_polarization_seed
        if args.exact_polarization_seed is not None
        else args.seed + 1701
    )
    proxy = run_model(
        model="proxy",
        triads=triads,
        rng=random.Random(args.seed + 1),
        axis=axis,
        tolerance=args.tolerance,
        normals=normals,
        depth2_trials_per_hit=args.depth2_trials_per_hit,
        proxy_frame_model=args.frame_model,
        proxy_frame_twist=args.frame_twist,
        exact_polarization_model=args.exact_polarization_model,
        exact_polarization_seed=exact_seed,
    )
    exact = run_model(
        model="exact_strain",
        triads=triads,
        rng=random.Random(args.seed + 2),
        axis=axis,
        tolerance=args.tolerance,
        normals=normals,
        depth2_trials_per_hit=args.depth2_trials_per_hit,
        proxy_frame_model=args.frame_model,
        proxy_frame_twist=args.frame_twist,
        exact_polarization_model=args.exact_polarization_model,
        exact_polarization_seed=exact_seed,
    )

    exact_delta = exact.zero_hits - proxy.zero_hits
    conclusion = (
        "diagnostic only: exact-strain finite-symbol branch "
        f"{'found more' if exact_delta > 0 else 'found fewer' if exact_delta < 0 else 'matched'} "
        "single-depth zero hits than the synthetic proxy under this seed; "
        "no proof, no theorem promotion, no Clay promotion."
    )
    return {
        "parameters": {
            "seed": args.seed,
            "samples_requested": args.samples,
            "triads_accepted": len(triads),
            "anti_parallel_rejects": anti_parallel_rejects,
            "tolerance": args.tolerance,
            "normals": args.normals,
            "axis": list(axis),
            "proxy_frame_model": args.frame_model,
            "proxy_frame_twist": args.frame_twist,
            "exact_polarization_model": args.exact_polarization_model,
            "exact_polarization_seed": exact_seed,
            "depth2_trials_per_hit": args.depth2_trials_per_hit,
        },
        "models": {
            "proxy": proxy.__dict__,
            "exact_strain": exact.__dict__,
        },
        "comparison": {
            "zero_hit_delta_exact_minus_proxy": exact_delta,
            "width_delta_exact_minus_proxy": (
                None
                if exact.estimated_width is None or proxy.estimated_width is None
                else exact.estimated_width - proxy.estimated_width
            ),
            "depth2_survival_delta_exact_minus_proxy": exact.depth2_survival - proxy.depth2_survival,
        },
        "conclusion": conclusion,
    }


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = build_report(args)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("NS exact-strain width comparison diagnostic")
        print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
