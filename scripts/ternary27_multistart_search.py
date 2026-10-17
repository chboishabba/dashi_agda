from __future__ import annotations

import numpy as np
from scipy.optimize import minimize

from ternary27_routeC_search import Ternary27RouteC


def free_vector(problem: Ternary27RouteC, coeff: np.ndarray) -> np.ndarray:
    return np.asarray([coeff[i] for i in problem.free_idx], dtype=float)


def full_from_free(problem: Ternary27RouteC, free: np.ndarray) -> np.ndarray:
    return problem.embed(free)


def solve_from(problem: Ternary27RouteC, seed: np.ndarray, delta_c=1.0, maxiter=180):
    result = minimize(
        lambda x: problem.objective(x, delta_c),
        np.asarray(seed, dtype=float),
        method="L-BFGS-B",
        bounds=[(-0.18, 0.18)] * len(problem.free_idx),
        options={"maxiter": maxiter, "ftol": 1e-10, "maxls": 40},
    )
    coeff = full_from_free(problem, result.x)
    return result, coeff, problem.metrics(coeff)


def sparse_pair_seed(problem: Ternary27RouteC) -> np.ndarray:
    coeff = np.zeros(27)
    coeff[1] = 0.18
    coeff[20] = 0.15
    return free_vector(problem, coeff)


def multistart(problem: Ternary27RouteC, random_starts=5, random_scale=0.06,
               seed_value=7, delta_c=1.0):
    rng = np.random.default_rng(seed_value)
    starts = [("zero", np.zeros(len(problem.free_idx))),
              ("sparse-pair", sparse_pair_seed(problem))]
    for i in range(random_starts):
        starts.append((f"random-{i}", rng.uniform(-random_scale, random_scale,
                                                 size=len(problem.free_idx))))
    rows = []
    for name, seed in starts:
        result, coeff, metrics = solve_from(problem, seed, delta_c=delta_c)
        rows.append((float(result.fun), name, metrics, coeff))
    rows.sort(key=lambda row: row[0])
    return rows


if __name__ == "__main__":
    p = Ternary27RouteC(nth=10, nz=12)
    for objective, name, metrics, coeff in multistart(p):
        active = [(i, float(v)) for i, v in enumerate(coeff) if abs(v) > 1e-5]
        print(name, objective, metrics, active)
