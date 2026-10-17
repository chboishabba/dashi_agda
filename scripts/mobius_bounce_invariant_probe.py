from __future__ import annotations
from typing import Mapping, Sequence
import math
import numpy as np


def mobius_shifted_field(
    s,
    alpha: float,
    rho: float,
    eps0: float = 0.32,
    eps1: float = -0.18,
    delta0: float = 0.02,
    half_twist: float = 0.5,
):
    """Toy |B| landscape with a half-twist local frame.

    This is NOT a divergence-free finite-beta equilibrium construction. It is a
    hypothesis generator for trapped-particle bounce-action geometry.
    """
    u = s - half_twist * alpha
    eps = eps0 + eps1 * rho
    delta = delta0 * rho
    return 1.0 - eps * np.cos(u) + delta * np.cos(2.0 * u)


def bounce_action(field, turning_field: float, n: int = 20001) -> float:
    """Dimensionless toy J_parallel proportional to integral sqrt(1-B/Bt) dl."""
    if turning_field <= 0:
        raise ValueError("turning_field must be positive")
    s = np.linspace(-math.pi, math.pi, n)
    B = np.asarray(field(s), dtype=float)
    allowed = B < turning_field
    i0 = int(np.argmin(B))
    if not bool(allowed[i0]):
        raise ValueError("selected turning field does not trap around the minimum")

    shift = n // 2 - i0
    integrand = np.roll(np.sqrt(np.maximum(0.0, 1.0 - B / turning_field)), shift)
    mask = np.roll(allowed, shift)
    mid = n // 2
    left = mid
    while left > 0 and mask[left - 1]:
        left -= 1
    right = mid
    while right < n - 1 and mask[right + 1]:
        right += 1
    x = np.linspace(-math.pi, math.pi, n)
    return float(np.trapezoid(integrand[left : right + 1], x[left : right + 1]))


def alpha_spread(values: Sequence[float]) -> float:
    values = np.asarray(values, dtype=float)
    return float(np.max(values) - np.min(values))


def maximum_j_violations(radial_mean_J: Sequence[float], tolerance: float = 1e-10) -> int:
    """Count outward increases of J; ideal maximum-J toy target is non-increasing."""
    values = list(map(float, radial_mean_J))
    return sum(1 for left, right in zip(values, values[1:]) if right > left + tolerance)


def same_or_better_invariant(
    candidate: Mapping[str, float], reference: Mapping[str, float]
) -> bool:
    """No-worse trapped-particle benchmark on declared defect coordinates."""
    keys = ("alpha_spread", "maxJ_violations", "radial_drift_defect")
    return all(float(candidate[key]) <= float(reference[key]) for key in keys)


if __name__ == "__main__":
    alphas = np.linspace(0, 2 * np.pi, 65, endpoint=False)
    radii = [0.2, 0.4, 0.6, 0.8]
    for turning_field in (0.90, 0.95, 1.00):
        means = []
        spreads = []
        for rho in radii:
            values = [
                bounce_action(
                    lambda s, a=alpha, r=rho: mobius_shifted_field(s, a, r),
                    turning_field,
                )
                for alpha in alphas
            ]
            means.append(float(np.mean(values)))
            spreads.append(alpha_spread(values))
        print(
            turning_field,
            "max_alpha_spread",
            max(spreads),
            "maxJ_violations",
            maximum_j_violations(means),
            "radial_means",
            means,
        )
