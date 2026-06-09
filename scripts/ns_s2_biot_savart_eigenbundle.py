#!/usr/bin/env python3
"""Local angular S^2 Biot-Savart/curl eigenbundle diagnostic.

This module implements the sprint's pointwise angular formula on the unit
sphere.  For

    c = (sin(psi) cos(phi), sin(psi) sin(phi), cos(psi)),

it builds the spherical tangent basis e_psi/e_phi, the prescribed local
two-by-two symbol m, the branch angle beta, the top direction e_plus, and the
associated normalized curl/Biot-Savart direction omega_hat = normalize(c x
e_plus).

The functions here are finite-dimensional local angular diagnostics only.
They are not a PDE proof, not a Biot-Savart closure theorem, and not an
analytic regularity result.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Iterable


Vec3 = tuple[float, float, float]

EPS = 1.0e-12


@dataclass(frozen=True)
class S2Basis:
    """Spherical unit direction and tangent frame."""

    psi: float
    phi: float
    c: Vec3
    e_psi: Vec3
    e_phi: Vec3


@dataclass(frozen=True)
class AngularEigenbundle:
    """Local angular eigenbundle from the sprint formula."""

    basis: S2Basis
    m11: float
    m12: float
    beta: float
    e_plus: Vec3
    omega_hat: Vec3


@dataclass(frozen=True)
class ResidualFamilies:
    """Single-depth residual families for the local angular omega direction."""

    family_i_parallel_pc_b: float
    family_ii_perp_pc_a: float
    min_residual: float
    hit_family: str


@dataclass(frozen=True)
class LambdaTriadDiagnostic:
    """Triad diagnostic value and its two multiplicative factors."""

    a: Vec3
    b: Vec3
    c: Vec3
    omega_hat: Vec3
    projected_b_norm_sq: float
    transverse_b_factor: float
    a_alignment_factor: float
    lambda_value: float
    residuals: ResidualFamilies


@dataclass(frozen=True)
class Depth2Diagnostic:
    """Depth-2 composition: first (a,b)->c, then (c,d)->e."""

    first: LambdaTriadDiagnostic
    second: LambdaTriadDiagnostic
    product_lambda: float
    min_lambda: float
    max_residual: float


def vec3(values: Iterable[float]) -> Vec3:
    xs = tuple(float(x) for x in values)
    if len(xs) != 3:
        raise ValueError("Vec3 requires exactly three coordinates")
    return (xs[0], xs[1], xs[2])


def add(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])


def sub(u: Vec3, v: Vec3) -> Vec3:
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])


def scale(s: float, u: Vec3) -> Vec3:
    return (s * u[0], s * u[1], s * u[2])


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


def project(c: Vec3, v: Vec3, eps: float = EPS) -> Vec3 | None:
    """Project v onto the tangent plane perpendicular to nonzero c."""

    c_hat = normalize(c, eps)
    if c_hat is None:
        return None
    return sub(v, scale(dot(v, c_hat), c_hat))


def parallel_residual(u: Vec3, v: Vec3, eps: float = EPS) -> float:
    nu = norm(u)
    nv = norm(v)
    if nu <= eps or nv <= eps:
        return 1.0
    return norm(cross(u, v)) / (nu * nv)


def spherical_basis_from_angles(psi: float, phi: float) -> S2Basis:
    """Build c, e_psi, e_phi from spherical angles."""

    s = math.sin(psi)
    cpsi = math.cos(psi)
    cphi = math.cos(phi)
    sphi = math.sin(phi)
    c = (s * cphi, s * sphi, cpsi)
    e_psi = (cpsi * cphi, cpsi * sphi, -s)
    e_phi = (-sphi, cphi, 0.0)
    return S2Basis(psi=psi, phi=phi, c=c, e_psi=e_psi, e_phi=e_phi)


def angles_from_unit(c: Vec3, eps: float = EPS) -> tuple[float, float] | None:
    c_hat = normalize(c, eps)
    if c_hat is None:
        return None
    z = max(-1.0, min(1.0, c_hat[2]))
    return math.acos(z), math.atan2(c_hat[1], c_hat[0])


def angular_eigenbundle_from_angles(psi: float, phi: float, eps: float = EPS) -> AngularEigenbundle | None:
    """Evaluate the sprint local angular eigenbundle formula."""

    basis = spherical_basis_from_angles(psi, phi)
    sin_psi = math.sin(psi)
    cos_psi = math.cos(psi)
    m11 = 0.5 * (cos_psi * cos_psi - sin_psi * sin_psi * math.cos(2.0 * phi))
    m12 = -0.5 * sin_psi * sin_psi * math.sin(2.0 * phi)
    beta = 0.5 * math.atan2(m12, m11)
    e_plus = add(scale(math.cos(beta), basis.e_psi), scale(math.sin(beta), basis.e_phi))
    omega_hat = normalize(cross(basis.c, e_plus), eps)
    if omega_hat is None:
        return None
    return AngularEigenbundle(
        basis=basis,
        m11=m11,
        m12=m12,
        beta=beta,
        e_plus=e_plus,
        omega_hat=omega_hat,
    )


def angular_eigenbundle(c: Vec3, eps: float = EPS) -> AngularEigenbundle | None:
    """Evaluate the local angular eigenbundle at a nonzero direction c."""

    angles = angles_from_unit(c, eps)
    if angles is None:
        return None
    psi, phi = angles
    return angular_eigenbundle_from_angles(psi, phi, eps)


def residual_families(a: Vec3, b: Vec3, c: Vec3 | None = None, eps: float = EPS) -> ResidualFamilies | None:
    """Compute the two local zero-mode residual families at c=normalize(a+b)."""

    c_hat = normalize(add(a, b), eps) if c is None else normalize(c, eps)
    if c_hat is None:
        return None
    bundle = angular_eigenbundle(c_hat, eps)
    if bundle is None:
        return None

    pc_b = project(c_hat, b, eps)
    pc_a = project(c_hat, a, eps)
    if pc_b is None or pc_a is None:
        return None

    family_i = parallel_residual(bundle.omega_hat, pc_b, eps)
    pc_a_norm = norm(pc_a)
    family_ii = abs(dot(bundle.omega_hat, pc_a)) / pc_a_norm if pc_a_norm > eps else 1.0
    min_res = min(family_i, family_ii)
    if abs(family_i - family_ii) <= 1.0e-15:
        hit_family = "both"
    elif family_i < family_ii:
        hit_family = "family_i"
    else:
        hit_family = "family_ii"
    return ResidualFamilies(
        family_i_parallel_pc_b=family_i,
        family_ii_perp_pc_a=family_ii,
        min_residual=min_res,
        hit_family=hit_family,
    )


def lambda_ns_triad(a: Vec3, b: Vec3, eps: float = EPS) -> LambdaTriadDiagnostic | None:
    """Evaluate the requested local angular lambda_NS triad diagnostic.

    lambda_NS(a,b) =

        ||(I - omega omega^T) P_c b||^2 / ||P_c b||^2
        * (a_hat dot omega)^2,

    where c = normalize(a+b), omega = omega_hat(c), and P_c is tangent
    projection onto c^perp.
    """

    a_hat = normalize(a, eps)
    c_hat = normalize(add(a, b), eps)
    if a_hat is None or c_hat is None:
        return None
    bundle = angular_eigenbundle(c_hat, eps)
    pc_b = project(c_hat, b, eps)
    if bundle is None or pc_b is None:
        return None

    pc_b_norm_sq = norm_sq(pc_b)
    if pc_b_norm_sq <= eps * eps:
        return None

    omega_component = scale(dot(pc_b, bundle.omega_hat), bundle.omega_hat)
    transverse_b = sub(pc_b, omega_component)
    transverse_b_factor = norm_sq(transverse_b) / pc_b_norm_sq
    a_alignment_factor = dot(a_hat, bundle.omega_hat) ** 2
    residuals = residual_families(a, b, c_hat, eps)
    if residuals is None:
        return None
    return LambdaTriadDiagnostic(
        a=a_hat,
        b=normalize(b, eps) or b,
        c=c_hat,
        omega_hat=bundle.omega_hat,
        projected_b_norm_sq=pc_b_norm_sq,
        transverse_b_factor=transverse_b_factor,
        a_alignment_factor=a_alignment_factor,
        lambda_value=transverse_b_factor * a_alignment_factor,
        residuals=residuals,
    )


def depth2(a: Vec3, b: Vec3, d: Vec3, eps: float = EPS) -> Depth2Diagnostic | None:
    """Compose two local angular triad diagnostics: (a,b)->c and (c,d)->e."""

    first = lambda_ns_triad(a, b, eps)
    if first is None:
        return None
    second = lambda_ns_triad(first.c, d, eps)
    if second is None:
        return None
    return Depth2Diagnostic(
        first=first,
        second=second,
        product_lambda=first.lambda_value * second.lambda_value,
        min_lambda=min(first.lambda_value, second.lambda_value),
        max_residual=max(first.residuals.min_residual, second.residuals.min_residual),
    )


def _assert_close(label: str, actual: float, expected: float = 0.0, tol: float = 1.0e-10) -> None:
    if abs(actual - expected) > tol:
        raise AssertionError(f"{label}: got {actual}, expected {expected} within {tol}")


def _round_vec(v: Vec3) -> list[float]:
    return [round(v[0], 10), round(v[1], 10), round(v[2], 10)]


def _rounded_dataclass(value: object) -> object:
    def convert(x: object) -> object:
        if isinstance(x, float):
            return round(x, 10)
        if isinstance(x, tuple):
            return [convert(y) for y in x]
        if isinstance(x, list):
            return [convert(y) for y in x]
        if isinstance(x, dict):
            return {k: convert(v) for k, v in x.items()}
        return x

    return convert(asdict(value))  # type: ignore[arg-type]


def run_self_test() -> dict[str, object]:
    """Run fast deterministic invariant checks for the local angular formula."""

    sample = angular_eigenbundle_from_angles(1.1, 0.7)
    if sample is None:
        raise AssertionError("angular sample unexpectedly failed")

    b = sample.basis
    _assert_close("c norm", norm(b.c), 1.0)
    _assert_close("e_psi norm", norm(b.e_psi), 1.0)
    _assert_close("e_phi norm", norm(b.e_phi), 1.0)
    _assert_close("c/e_psi orthogonal", dot(b.c, b.e_psi))
    _assert_close("c/e_phi orthogonal", dot(b.c, b.e_phi))
    _assert_close("e_psi/e_phi orthogonal", dot(b.e_psi, b.e_phi))
    _assert_close("e_plus norm", norm(sample.e_plus), 1.0)
    _assert_close("omega norm", norm(sample.omega_hat), 1.0)
    _assert_close("omega tangent", dot(sample.omega_hat, b.c))
    _assert_close("omega/e_plus orthogonal", dot(sample.omega_hat, sample.e_plus))

    a0 = normalize((1.0, 2.0, -0.5))
    b0 = normalize((-0.25, 0.7, 1.0))
    d0 = normalize((0.4, -0.8, 0.3))
    if a0 is None or b0 is None or d0 is None:
        raise AssertionError("nonzero samples failed normalization")

    c0 = normalize(add(a0, b0))
    if c0 is None:
        raise AssertionError("non-antipodal triad failed")
    pc_b = project(c0, b0)
    pc_a = project(c0, a0)
    if pc_b is None or pc_a is None:
        raise AssertionError("projection failed")
    _assert_close("P_c b tangent", dot(c0, pc_b))
    _assert_close("P_c a tangent", dot(c0, pc_a))

    lam = lambda_ns_triad(a0, b0)
    if lam is None:
        raise AssertionError("lambda diagnostic unexpectedly failed")
    for label, value in (
        ("transverse_b_factor", lam.transverse_b_factor),
        ("a_alignment_factor", lam.a_alignment_factor),
        ("lambda_value", lam.lambda_value),
        ("family_i", lam.residuals.family_i_parallel_pc_b),
        ("family_ii", lam.residuals.family_ii_perp_pc_a),
    ):
        if not (-1.0e-12 <= value <= 1.0 + 1.0e-12):
            raise AssertionError(f"{label} out of [0,1]: {value}")

    degenerate = lambda_ns_triad((1.0, 0.0, 0.0), (-1.0, 0.0, 0.0))
    if degenerate is not None:
        raise AssertionError("antipodal triad did not fail closed")

    d2 = depth2(a0, b0, d0)
    if d2 is None:
        raise AssertionError("depth2 diagnostic unexpectedly failed")

    return {
        "status": "ok",
        "module": "ns_s2_biot_savart_eigenbundle",
        "scope": "local_angular_diagnostic_not_pde_proof",
        "sample_c": _round_vec(b.c),
        "sample_e_plus": _round_vec(sample.e_plus),
        "sample_omega_hat": _round_vec(sample.omega_hat),
        "lambda_value": round(lam.lambda_value, 10),
        "residual_min": round(lam.residuals.min_residual, 10),
        "depth2_product_lambda": round(d2.product_lambda, 10),
        "antipodal_fail_closed": degenerate is None,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="run deterministic invariant checks")
    parser.add_argument("--a", nargs=3, type=float, help="first triad direction for lambda_ns_triad")
    parser.add_argument("--b", nargs=3, type=float, help="second triad direction for lambda_ns_triad")
    parser.add_argument("--d", nargs=3, type=float, help="optional depth-2 continuation direction")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if args.self_test:
        print(json.dumps(run_self_test(), indent=2, sort_keys=True))
        return 0

    if args.a is not None or args.b is not None:
        if args.a is None or args.b is None:
            raise ValueError("--a and --b must be supplied together")
        a = vec3(args.a)
        b = vec3(args.b)
        if args.d is not None:
            result = depth2(a, b, vec3(args.d))
            if result is None:
                print(json.dumps({"status": "degenerate"}, sort_keys=True))
                return 1
            print(json.dumps(_rounded_dataclass(result), indent=2, sort_keys=True))
            return 0
        result = lambda_ns_triad(a, b)
        if result is None:
            print(json.dumps({"status": "degenerate"}, sort_keys=True))
            return 1
        print(json.dumps(_rounded_dataclass(result), indent=2, sort_keys=True))
        return 0

    print(
        json.dumps(
            {
                "module": "ns_s2_biot_savart_eigenbundle",
                "available": True,
                "scope": "local_angular_diagnostic_not_pde_proof",
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
