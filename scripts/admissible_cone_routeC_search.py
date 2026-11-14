from __future__ import annotations

import math
import numpy as np


def abc_seed(delta: float, mach_share: float = 0.7) -> np.ndarray:
    if not 0.0 <= delta <= 1.0:
        raise ValueError("delta must lie in [0,1]")
    if not 0.0 <= mach_share <= 1.0:
        raise ValueError("mach_share must lie in [0,1]")
    available = max(0.0, 1.0 - delta)
    mach = mach_share * math.sqrt(available)
    alpha = 1.0 - delta - mach * mach
    return np.array([mach, alpha, delta, 0.0, 0.0, 0.0, 0.0], dtype=float)


def equality_constraints(state: np.ndarray, delta_target: float) -> np.ndarray:
    mach, alpha, delta = state[:3]
    return np.array([
        mach * mach + alpha + delta - 1.0,
        delta - delta_target,
    ], dtype=float)


def equality_jacobian(state: np.ndarray) -> np.ndarray:
    mach = float(state[0])
    return np.array([
        [2.0 * mach, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0],
    ], dtype=float)


def nullspace(jacobian: np.ndarray, tolerance: float = 1e-10) -> np.ndarray:
    _, singular, vh = np.linalg.svd(jacobian, full_matrices=True)
    rank = int(np.sum(singular > tolerance))
    return vh[rank:].T


def project_to_tangent(vector: np.ndarray, basis: np.ndarray) -> np.ndarray:
    return basis @ (basis.T @ vector)


def inequality_admissible(
    state: np.ndarray,
    coeff_bound: float = 0.45,
    tolerance: float = 1e-10,
) -> bool:
    mach, alpha, delta = state[:3]
    return (
        -tolerance <= mach < 1.0 + tolerance
        and alpha >= -tolerance
        and -tolerance <= delta <= 1.0 + tolerance
        and np.all(np.abs(state[3:]) <= coeff_bound + tolerance)
    )


def admissible(
    state: np.ndarray,
    delta_target: float,
    coeff_bound: float = 0.45,
    tolerance: float = 1e-8,
) -> bool:
    return (
        np.max(np.abs(equality_constraints(state, delta_target))) <= tolerance
        and inequality_admissible(state, coeff_bound=coeff_bound, tolerance=tolerance)
    )


def c3n_allowed_harmonic(mode: int, ternary_depth: int) -> bool:
    if ternary_depth < 1:
        raise ValueError("ternary_depth must be >= 1")
    sectors = 3 ** ternary_depth
    return mode % sectors == 0


def projected_descent_direction(
    state: np.ndarray,
    gradient: np.ndarray,
) -> np.ndarray:
    basis = nullspace(equality_jacobian(state))
    return -project_to_tangent(gradient, basis)


def continuation_schedule(steps: int) -> np.ndarray:
    if steps < 2:
        raise ValueError("steps must be >= 2")
    return np.linspace(0.0, 1.0, steps)


def continuation_states(steps: int, mach_share: float = 0.7) -> list[np.ndarray]:
    return [abc_seed(float(delta), mach_share=mach_share) for delta in continuation_schedule(steps)]


if __name__ == "__main__":
    for state, target in zip(continuation_states(5), continuation_schedule(5)):
        J = equality_jacobian(state)
        N = nullspace(J)
        print(
            "delta", target,
            "state", state[:3],
            "nullity", N.shape[1],
            "jacobian_null_residual", float(np.linalg.norm(J @ N)),
            "admissible", admissible(state, float(target)),
        )
