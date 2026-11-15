from __future__ import annotations

import math


def alfvenic_inertia_minus_tension(B2: float, mu0: float, rho: float) -> float:
    """Coefficient residual for rho(u.grad)u - JxB with u^2=B^2/(mu0 rho)."""
    if B2 < 0 or mu0 <= 0 or rho <= 0:
        raise ValueError("require B2 >= 0, mu0 > 0, rho > 0")
    u2 = B2 / (mu0 * rho)
    return rho * u2 - B2 / mu0


def cgl_tension_residual(B2: float, mu0: float, delta_p: float) -> float:
    """Coefficient residual div(P)-JxB along kappa for constant CGL pressures."""
    if B2 < 0 or mu0 <= 0:
        raise ValueError("require B2 >= 0, mu0 > 0")
    return delta_p - B2 / mu0


def firehose_margin(B2: float, mu0: float, delta_p: float) -> float:
    """Positive is inside the simple CGL firehose-stable side; zero is marginal."""
    return B2 / mu0 - delta_p


def _basis(theta: float, zeta: float):
    e_theta = (
        -math.sin(theta) * math.cos(zeta),
        -math.sin(theta) * math.sin(zeta),
        math.cos(theta),
    )
    e_zeta = (-math.sin(zeta), math.cos(zeta), 0.0)
    normal = (
        math.cos(theta) * math.cos(zeta),
        math.cos(theta) * math.sin(zeta),
        math.sin(theta),
    )
    return e_theta, e_zeta, normal


def _field_unit(theta: float, zeta: float, R0: float, r: float, B0: float, C: float):
    h = R0 + r * math.cos(theta)
    B_theta = C / h
    B_zeta_sq = B0 * B0 - B_theta * B_theta
    if B_zeta_sq <= 0:
        raise ValueError("field reality condition failed")
    B_zeta = math.sqrt(B_zeta_sq)
    e_theta, e_zeta, normal = _basis(theta, zeta)
    b = tuple((B_theta * e_theta[i] + B_zeta * e_zeta[i]) / B0 for i in range(3))
    return b, normal, B_theta, B_zeta, h


def circular_seed_geodesic_curvature_rms(
    R0: float = 3.0,
    r: float = 1.0,
    B0: float = 1.0,
    C: float = 0.5,
    samples: int = 8000,
    ds: float = 1e-4,
) -> float:
    """RMS surface-tangential curvature of the explicit constant-|B| torus seed.

    Nonzero output falsifies the shortcut that this circular-torus seed already
    solves route-C scalar-pressure force balance.  This is a geometry probe, not
    a full finite-orbit-width calculation.
    """
    if not (R0 > r > 0 and B0 > 0 and samples >= 100):
        raise ValueError("require R0 > r > 0, B0 > 0, samples >= 100")
    theta = 0.17
    zeta = 0.0
    sq = 0.0
    for _ in range(samples):
        b, normal, B_theta, B_zeta, h = _field_unit(theta, zeta, R0, r, B0, C)
        dtheta_ds = B_theta / (B0 * r)
        dzeta_ds = B_zeta / (B0 * h)
        theta2 = theta + dtheta_ds * ds
        zeta2 = zeta + dzeta_ds * ds
        b2, _, _, _, _ = _field_unit(theta2, zeta2, R0, r, B0, C)
        kappa = tuple((b2[i] - b[i]) / ds for i in range(3))
        kn = sum(kappa[i] * normal[i] for i in range(3))
        kt = tuple(kappa[i] - kn * normal[i] for i in range(3))
        sq += sum(x * x for x in kt)
        theta, zeta = theta2, zeta2
    return math.sqrt(sq / samples)


def inverse_phase(p: int) -> int:
    """C3 additive phase inversion: 0->0, 1<->2."""
    if p not in (0, 1, 2):
        raise ValueError("phase must be 0,1,2")
    return (-p) % 3
