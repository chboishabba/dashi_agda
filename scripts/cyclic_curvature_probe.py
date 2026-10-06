from __future__ import annotations
import math


def triad_vectors(magnitude: float, phase0: float = 0.0):
    return [
        (
            magnitude * math.cos(phase0 + 2.0 * math.pi * j / 3.0),
            magnitude * math.sin(phase0 + 2.0 * math.pi * j / 3.0),
        )
        for j in range(3)
    ]


def vector_sum(vectors):
    return tuple(sum(v[i] for v in vectors) for i in range(2))


def triadic_children_sum_zero(magnitude: float, depth: int, phase0: float = 0.0) -> bool:
    """Check recursive C_(3^depth) equal-phase cancellation in the transverse plane."""
    if depth < 1:
        raise ValueError("depth must be >= 1")
    phases = [phase0]
    for _ in range(depth):
        phases = [p + 2.0 * math.pi * j / 3.0 for p in phases for j in range(3)]
    sx = sum(magnitude * math.cos(p) for p in phases)
    sy = sum(magnitude * math.sin(p) for p in phases)
    return math.hypot(sx, sy) < 1e-10 * max(1.0, magnitude * len(phases))


def _curve(t: float, R: float, r: float, m: int):
    return (
        (R + r * math.cos(m * t)) * math.cos(t),
        (R + r * math.cos(m * t)) * math.sin(t),
        r * math.sin(m * t),
    )


def torus_helix_radial_curvature_mean(R: float, r: float, m: int, samples: int = 1200) -> float:
    """Numerical mean kappa·n for a naive circular-torus helix.

    This is a falsification probe for the claim that more helical winding alone
    cancels radial curvature. It is not a guiding-centre transport calculation.
    """
    if R <= r or r <= 0 or samples < 100:
        raise ValueError("require R > r > 0 and samples >= 100")
    h = 1e-5
    vals = []
    for q in range(samples):
        t = 2.0 * math.pi * q / samples
        p0 = _curve(t, R, r, m)
        pm = _curve(t - h, R, r, m)
        pp = _curve(t + h, R, r, m)
        d1 = tuple((pp[i] - pm[i]) / (2.0 * h) for i in range(3))
        d2 = tuple((pp[i] - 2.0 * p0[i] + pm[i]) / (h * h) for i in range(3))
        speed = math.sqrt(sum(x * x for x in d1))
        tangent = tuple(x / speed for x in d1)
        tangent_d2 = sum(tangent[i] * d2[i] for i in range(3))
        kappa = tuple((d2[i] - tangent[i] * tangent_d2) / (speed * speed) for i in range(3))
        normal = (
            math.cos(m * t) * math.cos(t),
            math.cos(m * t) * math.sin(t),
            math.sin(m * t),
        )
        vals.append(sum(kappa[i] * normal[i] for i in range(3)))
    return sum(vals) / len(vals)
