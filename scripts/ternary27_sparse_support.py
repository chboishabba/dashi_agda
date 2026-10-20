from __future__ import annotations

import numpy as np
from scipy.optimize import minimize

from ternary27_routeC_search import Ternary27RouteC


def ranked_support(coeff: np.ndarray, excluded=(0, 9, 18)) -> list[int]:
    excluded = set(excluded)
    return [int(i) for i in np.argsort(np.abs(coeff))[::-1] if int(i) not in excluded]


def optimize_on_support(problem: Ternary27RouteC, support: list[int], delta_c: float,
                        seed: np.ndarray | None = None, maxiter: int = 120):
    support = [int(i) for i in support]
    if seed is None:
        seed = np.zeros(len(support))
    else:
        seed = np.asarray(seed, dtype=float)

    def embed(values):
        coeff = np.zeros(27)
        coeff[support] = values
        return coeff

    result = minimize(
        lambda values: problem.objective(
            np.asarray([embed(values)[i] for i in problem.free_idx]), delta_c
        ),
        seed,
        method="L-BFGS-B",
        bounds=[(-0.18, 0.18)] * len(support),
        options={"maxiter": maxiter, "ftol": 1e-10},
    )
    coeff = embed(result.x)
    return result, coeff, problem.metrics(coeff)


def support_retention(full_objective: float, full_metrics: dict,
                      objective: float, metrics: dict,
                      objective_ratio=1.05, b_abs_slack=0.003,
                      kg_ratio=1.01, minimum_minor_radius=0.35) -> bool:
    return (
        objective <= objective_ratio * full_objective
        and metrics["relative_B_spread"] <= full_metrics["relative_B_spread"] + b_abs_slack
        and metrics["geodesic_curvature_rms"] <= kg_ratio * full_metrics["geodesic_curvature_rms"]
        and metrics["minimum_minor_radius"] > minimum_minor_radius
    )


def sparse_scan(problem: Ternary27RouteC, delta_c=1.0, max_support=10):
    rows = problem.continuation(levels=(delta_c,), maxiter=160)
    _, full_objective, full_metrics, full_coeff = rows[-1]
    order = ranked_support(full_coeff)
    out = []
    for k in range(1, max_support + 1):
        support = order[:k]
        seed = full_coeff[support]
        result, coeff, metrics = optimize_on_support(problem, support, delta_c, seed=seed)
        accepted = support_retention(full_objective, full_metrics, result.fun, metrics)
        out.append((k, support, result.fun, metrics, coeff, accepted))
    return full_objective, full_metrics, full_coeff, out


if __name__ == "__main__":
    p = Ternary27RouteC(nth=16, nz=18)
    full_objective, full_metrics, full_coeff, rows = sparse_scan(p)
    print("full", full_objective, full_metrics)
    for row in rows:
        k, support, objective, metrics, _, accepted = row
        print(k, support, objective, metrics, accepted)
