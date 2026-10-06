from __future__ import annotations

import math


def _curve(t: float, R: float, r: float, m: int, phase: float):
    theta = m * t + phase
    return (
        (R + r * math.cos(theta)) * math.cos(t),
        (R + r * math.cos(theta)) * math.sin(t),
        r * math.sin(theta),
    )


def _dot(a, b):
    return sum(a[i] * b[i] for i in range(3))


def _norm(a):
    return math.sqrt(_dot(a, a))


def _scale(a, c):
    return tuple(c * x for x in a)


def _cross(a, b):
    return (
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    )


def radial_curvature_drift_proxy(
    t: float,
    R: float,
    r: float,
    m: int,
    phase: float,
    h: float = 1e-4,
) -> float:
    """Radial projection of b x kappa for a circular-torus helix.

    Overall particle-dependent prefactors are omitted; this isolates the geometry
    entering the guiding-centre curvature drift.  It is a geometry probe, not a
    full-orbit transport solver.
    """
    if R <= r or r <= 0.0:
        raise ValueError("require R > r > 0")
    p0 = _curve(t, R, r, m, phase)
    pm = _curve(t - h, R, r, m, phase)
    pp = _curve(t + h, R, r, m, phase)
    d1 = tuple((pp[i] - pm[i]) / (2.0 * h) for i in range(3))
    d2 = tuple((pp[i] - 2.0 * p0[i] + pm[i]) / (h * h) for i in range(3))
    speed = _norm(d1)
    tangent = _scale(d1, 1.0 / speed)
    tangential_d2 = _dot(tangent, d2)
    kappa = tuple(
        (d2[i] - tangent[i] * tangential_d2) / (speed * speed)
        for i in range(3)
    )
    drift = _cross(tangent, kappa)
    theta = m * t + phase
    outward_normal = (
        math.cos(theta) * math.cos(t),
        math.cos(theta) * math.sin(t),
        math.sin(theta),
    )
    return _dot(drift, outward_normal)


def cyclic_radial_curvature_drift_residual(
    R: float,
    r: float,
    m: int,
    sectors: int,
    samples: int = 1200,
) -> float:
    if sectors <= 0 or samples < 100:
        raise ValueError("sectors must be positive and samples >= 100")
    values = []
    for q in range(samples):
        t = 2.0 * math.pi * q / samples
        average = sum(
            radial_curvature_drift_proxy(
                t, R, r, m, 2.0 * math.pi * j / sectors
            )
            for j in range(sectors)
        ) / sectors
        values.append(average)
    return math.sqrt(sum(x * x for x in values) / len(values))


def single_phase_radial_curvature_drift_rms(
    R: float,
    r: float,
    m: int,
    samples: int = 1200,
) -> float:
    values = [
        radial_curvature_drift_proxy(2.0 * math.pi * q / samples, R, r, m, 0.0)
        for q in range(samples)
    ]
    return math.sqrt(sum(x * x for x in values) / len(values))
