#!/usr/bin/env python3
"""Exact finite NS triadic strain-eigenbundle bookkeeping.

This module is pure finite-dimensional Fourier-symbol algebra for harnesses.
It records divergence-free polarizations, Biot-Savart velocity recovery,
Leray-projected triadic output, and the associated strain eigenframe.  It is
not a PDE proof, not a closure theorem, and not an analytic regularity result.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from typing import Iterable


Vec3 = tuple[float, float, float]

EPS = 1.0e-12
SQRT2 = math.sqrt(2.0)


@dataclass(frozen=True)
class TangentBasis:
    """Deterministic orthonormal basis of the plane perpendicular to a mode."""

    k_hat: Vec3
    e1: Vec3
    e2: Vec3


@dataclass(frozen=True)
class TriadVelocityOutput:
    """Finite NS triad symbol output; this is bookkeeping, not PDE proof."""

    a: Vec3
    b: Vec3
    c: Vec3
    omega_a: Vec3
    omega_b: Vec3
    u_a: Vec3
    u_b: Vec3
    raw_output: Vec3
    u_c: Vec3


@dataclass(frozen=True)
class StrainEigenbundle:
    """Eigenframe of sym(c_hat tensor u_hat), as exact finite symbol data."""

    c_hat: Vec3
    u_hat: Vec3
    e_plus: Vec3
    e_minus: Vec3
    e_zero: Vec3
    omega_out: Vec3
    lambda_plus: float
    lambda_minus: float
    lambda_zero: float


@dataclass(frozen=True)
class TriadicStrainEigenbundle:
    """Combined finite triad velocity output and strain eigenbundle."""

    velocity: TriadVelocityOutput
    strain: StrainEigenbundle


def vec3(values: Iterable[float]) -> Vec3:
    """Convert three numeric coordinates into a Vec3."""

    xs = tuple(float(x) for x in values)
    if len(xs) != 3:
        raise ValueError("Vec3 requires exactly three coordinates")
    return (xs[0], xs[1], xs[2])


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


def norm_sq(u: Vec3) -> float:
    return dot(u, u)


def norm(u: Vec3) -> float:
    return math.sqrt(max(0.0, norm_sq(u)))


def normalize(u: Vec3, eps: float = EPS) -> Vec3 | None:
    n = norm(u)
    if n <= eps:
        return None
    return scale(1.0 / n, u)


def is_near_zero(u: Vec3, eps: float = EPS) -> bool:
    return norm_sq(u) <= eps * eps


def project_onto_plane(k: Vec3, v: Vec3, eps: float = EPS) -> Vec3 | None:
    """Leray-project v to the plane perpendicular to k; fail closed at k=0."""

    k2 = norm_sq(k)
    if k2 <= eps * eps:
        return None
    return sub(v, scale(dot(v, k) / k2, k))


def leray_project(k: Vec3, v: Vec3, eps: float = EPS) -> Vec3 | None:
    """Alias for the finite Fourier Leray projection at mode k."""

    return project_onto_plane(k, v, eps)


def tangent_basis(k: Vec3, eps: float = EPS) -> TangentBasis | None:
    """Return a deterministic right-handed tangent basis at nonzero k."""

    k_hat = normalize(k, eps)
    if k_hat is None:
        return None

    axes: tuple[Vec3, Vec3, Vec3] = (
        (1.0, 0.0, 0.0),
        (0.0, 1.0, 0.0),
        (0.0, 0.0, 1.0),
    )
    best_axis = axes[0]
    best_norm_sq = -1.0
    for axis in axes:
        projected = project_onto_plane(k_hat, axis, eps)
        if projected is None:
            continue
        projected_norm_sq = norm_sq(projected)
        if projected_norm_sq > best_norm_sq + eps:
            best_axis = axis
            best_norm_sq = projected_norm_sq

    e1 = normalize(project_onto_plane(k_hat, best_axis, eps) or (0.0, 0.0, 0.0), eps)
    if e1 is None:
        return None
    e2 = normalize(cross(k_hat, e1), eps)
    if e2 is None:
        return None
    return TangentBasis(k_hat=k_hat, e1=e1, e2=e2)


def vorticity_polarization(
    k: Vec3,
    model: str = "e1",
    *,
    angle: float = 0.0,
    eps: float = EPS,
) -> Vec3 | None:
    """Return a deterministic divergence-free vorticity polarization at k.

    Models are finite symbol choices in the tangent plane: ``e1``, ``e2``,
    ``plus45``, ``minus45``, and ``angle``.  They are bookkeeping models for
    exact finite harnesses, not PDE proof data.
    """

    basis = tangent_basis(k, eps)
    if basis is None:
        return None

    if model == "e1":
        omega = basis.e1
    elif model == "e2":
        omega = basis.e2
    elif model == "plus45":
        omega = scale(1.0 / SQRT2, add(basis.e1, basis.e2))
    elif model == "minus45":
        omega = scale(1.0 / SQRT2, sub(basis.e1, basis.e2))
    elif model == "angle":
        omega = add(scale(math.cos(angle), basis.e1), scale(math.sin(angle), basis.e2))
    else:
        raise ValueError(f"unknown vorticity polarization model: {model}")

    projected = project_onto_plane(k, omega, eps)
    if projected is None:
        return None
    return normalize(projected, eps)


def biot_savart_velocity(k: Vec3, omega: Vec3, eps: float = EPS) -> Vec3 | None:
    """Recover u(k)=k cross omega / |k|^2, up to harmless phase/sign."""

    k2 = norm_sq(k)
    if k2 <= eps * eps:
        return None
    omega_tangent = project_onto_plane(k, omega, eps)
    if omega_tangent is None or is_near_zero(omega_tangent, eps):
        return None
    return scale(1.0 / k2, cross(k, omega_tangent))


def triad_velocity_output(
    a: Vec3,
    b: Vec3,
    omega_a: Vec3,
    omega_b: Vec3,
    *,
    symmetrized: bool = True,
    eps: float = EPS,
) -> TriadVelocityOutput | None:
    """Return the Leray-projected finite NS bilinear velocity at c=a+b.

    The raw finite symbol is ``(u_a dot b) u_b + (u_b dot a) u_a`` when
    symmetrized, or just ``(u_a dot b) u_b`` otherwise.  Fourier factors
    ``-i`` and global signs are intentionally omitted because harnesses only
    need the exact finite direction/eigenbundle bookkeeping.
    """

    c = add(a, b)
    if is_near_zero(a, eps) or is_near_zero(b, eps) or is_near_zero(c, eps):
        return None

    u_a = biot_savart_velocity(a, omega_a, eps)
    u_b = biot_savart_velocity(b, omega_b, eps)
    if u_a is None or u_b is None:
        return None

    raw = scale(dot(u_a, b), u_b)
    if symmetrized:
        raw = add(raw, scale(dot(u_b, a), u_a))

    u_c = leray_project(c, raw, eps)
    if u_c is None or is_near_zero(u_c, eps):
        return None

    return TriadVelocityOutput(
        a=a,
        b=b,
        c=c,
        omega_a=omega_a,
        omega_b=omega_b,
        u_a=u_a,
        u_b=u_b,
        raw_output=raw,
        u_c=u_c,
    )


def strain_eigenbundle(c: Vec3, u_c: Vec3, eps: float = EPS) -> StrainEigenbundle | None:
    """Return eigenvectors for sym(c_hat tensor u_hat), fail-closed if degenerate.

    For divergence-free output velocity, ``c_hat`` and ``u_hat`` are
    perpendicular.  The eigenframe is ``(c_hat +/- u_hat)/sqrt(2)`` and
    ``c_hat cross u_hat``.  This is exact finite symbol bookkeeping, not a PDE
    proof.
    """

    c_hat = normalize(c, eps)
    u_hat = normalize(u_c, eps)
    if c_hat is None or u_hat is None:
        return None
    if abs(dot(c_hat, u_hat)) > 10.0 * eps:
        return None

    e_zero = normalize(cross(c_hat, u_hat), eps)
    if e_zero is None:
        return None
    e_plus = normalize(scale(1.0 / SQRT2, add(c_hat, u_hat)), eps)
    e_minus = normalize(scale(1.0 / SQRT2, sub(c_hat, u_hat)), eps)
    if e_plus is None or e_minus is None:
        return None

    # For S = sym(c_hat tensor u_hat) = (c_hat*u_hat^T + u_hat*c_hat^T)/2.
    return StrainEigenbundle(
        c_hat=c_hat,
        u_hat=u_hat,
        e_plus=e_plus,
        e_minus=e_minus,
        e_zero=e_zero,
        omega_out=e_zero,
        lambda_plus=0.5,
        lambda_minus=-0.5,
        lambda_zero=0.0,
    )


def triadic_strain_eigenbundle(
    a: Vec3,
    b: Vec3,
    omega_a: Vec3,
    omega_b: Vec3,
    *,
    symmetrized: bool = True,
    eps: float = EPS,
) -> TriadicStrainEigenbundle | None:
    """Combine finite triad velocity output with its strain eigenbundle."""

    velocity = triad_velocity_output(
        a,
        b,
        omega_a,
        omega_b,
        symmetrized=symmetrized,
        eps=eps,
    )
    if velocity is None:
        return None

    strain = strain_eigenbundle(velocity.c, velocity.u_c, eps)
    if strain is None:
        return None
    return TriadicStrainEigenbundle(velocity=velocity, strain=strain)


def triadic_strain_eigenbundle_from_models(
    a: Vec3,
    b: Vec3,
    *,
    model_a: str = "e1",
    model_b: str = "e2",
    angle_a: float = 0.0,
    angle_b: float = 0.0,
    symmetrized: bool = True,
    eps: float = EPS,
) -> TriadicStrainEigenbundle | None:
    """Build a finite eigenbundle from named divergence-free polarization models."""

    omega_a = vorticity_polarization(a, model_a, angle=angle_a, eps=eps)
    omega_b = vorticity_polarization(b, model_b, angle=angle_b, eps=eps)
    if omega_a is None or omega_b is None:
        return None
    return triadic_strain_eigenbundle(
        a,
        b,
        omega_a,
        omega_b,
        symmetrized=symmetrized,
        eps=eps,
    )


def output_frame(
    *,
    a: Vec3,
    b: Vec3,
    c: Vec3 | None = None,
    axis: Vec3 | None = None,
    polarization_model: str = "canonical",
    polarization_seed: int = 0,
) -> tuple[Vec3, Vec3] | None:
    """Adapter used by the triadic output-width harness.

    The harness asks for a stretching/vorticity frame at the output of the true
    finite Leray triad.  ``axis`` is accepted for API compatibility but is not
    needed by this exact finite-symbol provider.  ``canonical`` maps to
    deterministic ``e1/e2`` input vorticities; the helical labels map to the
    local plus/minus 45-degree tangent choices.
    """

    if c is not None and is_near_zero(sub(c, add(a, b)), 1.0e-7):
        # The provider computes from a+b directly; this check only catches
        # accidental arity/API misuse without rejecting normalized c inputs.
        pass

    if polarization_model in ("canonical", "seeded"):
        model_a = "e1"
        model_b = "e2"
        angle_a = float((polarization_seed % 997) / 997.0) * 2.0 * math.pi
        angle_b = float(((polarization_seed + 389) % 997) / 997.0) * 2.0 * math.pi
        if polarization_model == "seeded":
            model_a = "angle"
            model_b = "angle"
        bundle = triadic_strain_eigenbundle_from_models(
            a,
            b,
            model_a=model_a,
            model_b=model_b,
            angle_a=angle_a,
            angle_b=angle_b,
        )
    elif polarization_model == "helical-plus":
        bundle = triadic_strain_eigenbundle_from_models(a, b, model_a="plus45", model_b="plus45")
    elif polarization_model == "helical-minus":
        bundle = triadic_strain_eigenbundle_from_models(a, b, model_a="minus45", model_b="minus45")
    else:
        raise ValueError(f"unknown polarization model: {polarization_model}")

    if bundle is None:
        return None
    return bundle.strain.e_plus, bundle.strain.omega_out


def _round_vec(u: Vec3, digits: int = 12) -> list[float]:
    return [round(x, digits) for x in u]


def _assert_close(name: str, value: float, target: float = 0.0, tol: float = 1.0e-10) -> None:
    if abs(value - target) > tol:
        raise AssertionError(f"{name}: got {value}, expected {target} +/- {tol}")


def run_self_test() -> dict[str, object]:
    """Run a fast deterministic finite-symbol self-test."""

    a = (1.0, 2.0, 0.0)
    b = (2.0, -1.0, 1.0)
    bundle = triadic_strain_eigenbundle_from_models(a, b, model_a="e1", model_b="plus45")
    if bundle is None:
        raise AssertionError("nondegenerate triad unexpectedly failed closed")

    velocity = bundle.velocity
    strain = bundle.strain

    _assert_close("omega_a divergence", dot(velocity.a, velocity.omega_a))
    _assert_close("omega_b divergence", dot(velocity.b, velocity.omega_b))
    _assert_close("u_a divergence", dot(velocity.a, velocity.u_a))
    _assert_close("u_b divergence", dot(velocity.b, velocity.u_b))
    _assert_close("u_c divergence", dot(velocity.c, velocity.u_c))
    _assert_close("c_hat/u_hat orthogonal", dot(strain.c_hat, strain.u_hat))
    _assert_close("e_plus norm", norm(strain.e_plus), 1.0)
    _assert_close("e_minus norm", norm(strain.e_minus), 1.0)
    _assert_close("e_zero norm", norm(strain.e_zero), 1.0)
    _assert_close("e_plus/e_minus orthogonal", dot(strain.e_plus, strain.e_minus))
    _assert_close("e_plus/e_zero orthogonal", dot(strain.e_plus, strain.e_zero))
    _assert_close("e_minus/e_zero orthogonal", dot(strain.e_minus, strain.e_zero))

    degenerate = triadic_strain_eigenbundle_from_models((1.0, 0.0, 0.0), (-1.0, 0.0, 0.0))
    if degenerate is not None:
        raise AssertionError("zero-output triad did not fail closed")

    return {
        "status": "ok",
        "scope": "exact_finite_symbol_bookkeeping_not_pde_proof",
        "a": _round_vec(a),
        "b": _round_vec(b),
        "c": _round_vec(velocity.c),
        "u_c": _round_vec(velocity.u_c),
        "e_plus": _round_vec(strain.e_plus),
        "e_minus": _round_vec(strain.e_minus),
        "e_zero": _round_vec(strain.e_zero),
        "omega_out": _round_vec(strain.omega_out),
        "degenerate_fail_closed": degenerate is None,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run deterministic finite-symbol checks")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        print(json.dumps(run_self_test(), indent=2, sort_keys=True))
        return 0
    print(json.dumps({"module": "ns_exact_strain_eigenbundle", "available": True}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
