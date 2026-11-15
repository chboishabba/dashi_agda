from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from scipy.optimize import minimize


@dataclass(frozen=True)
class RouteCMetrics:
    objective: float
    relative_b_std: float
    geodesic_curvature_rms: float
    surface_divergence_rms: float


def _dd_periodic(f: np.ndarray, axis: int, h: float) -> np.ndarray:
    return (np.roll(f, -1, axis=axis) - np.roll(f, 1, axis=axis)) / (2.0 * h)


class RouteCGeometryProblem:
    """Low-parameter C3-shaped toroidal geometry probe.

    This is an exploratory surface-field optimizer.  It constructs a tangent
    surface field from a stream function, so the continuum surface-divergence
    identity is built into the ansatz.  Finite-difference divergence is retained
    as a replay diagnostic.  The model is not a global vacuum/MHD coil solver.
    """

    def __init__(self, nth: int = 40, nz: int = 48, r0: float = 3.0, a0: float = 1.0):
        self.nth = nth
        self.nz = nz
        self.r0 = r0
        self.a0 = a0
        self.theta = np.linspace(0.0, 2.0 * np.pi, nth, endpoint=False)
        self.zeta = np.linspace(0.0, 2.0 * np.pi, nz, endpoint=False)
        self.TH, self.ZE = np.meshgrid(self.theta, self.zeta, indexing="ij")
        self.dth = 2.0 * np.pi / nth
        self.dze = 2.0 * np.pi / nz

    def evaluate(self, params: np.ndarray):
        c3, d3, s3, s6 = params
        phase = 3.0 * (self.TH - self.ZE)
        rho = self.a0 * (1.0 + c3 * np.cos(phase))
        zoff = self.a0 * d3 * np.sin(phase)

        rr = self.r0 + rho * np.cos(self.TH)
        zz = rho * np.sin(self.TH) + zoff
        x = rr * np.cos(self.ZE)
        y = rr * np.sin(self.ZE)
        r = np.stack([x, y, zz], axis=-1)

        e_th = _dd_periodic(r, 0, self.dth)
        e_ze = _dd_periodic(r, 1, self.dze)
        cross = np.cross(e_th, e_ze)
        sqrtg = np.linalg.norm(cross, axis=-1)
        normal = cross / sqrtg[..., None]

        iota0 = 0.42
        chi_th = 1.0 + 3.0 * s3 * np.cos(phase) + 6.0 * s6 * np.cos(2.0 * phase)
        chi_ze = -iota0 - 3.0 * s3 * np.cos(phase) - 6.0 * s6 * np.cos(2.0 * phase)

        b_th = chi_ze / sqrtg
        b_ze = -chi_th / sqrtg
        b_vec = b_th[..., None] * e_th + b_ze[..., None] * e_ze
        b_mag = np.linalg.norm(b_vec, axis=-1)
        bhat = b_vec / b_mag[..., None]
        bth_unit = b_th / b_mag
        bze_unit = b_ze / b_mag

        db_dth = _dd_periodic(bhat, 0, self.dth)
        db_dze = _dd_periodic(bhat, 1, self.dze)
        kappa = bth_unit[..., None] * db_dth + bze_unit[..., None] * db_dze
        q = np.cross(normal, bhat)
        q /= np.linalg.norm(q, axis=-1)[..., None]
        kappa_g = np.sum(kappa * q, axis=-1)

        divsurf = (
            _dd_periodic(sqrtg * b_th, 0, self.dth)
            + _dd_periodic(sqrtg * b_ze, 1, self.dze)
        ) / sqrtg

        return r, b_th, b_ze, b_mag, kappa_g, divsurf

    def objective(self, params: np.ndarray) -> float:
        _, _, _, bmag, kg, div = self.evaluate(params)
        bvar = np.std(bmag) / np.mean(bmag)
        kgrms = np.sqrt(np.mean(kg * kg))
        divrms = np.sqrt(np.mean(div * div))
        reg = 0.03 * float(np.sum(params * params))
        return float(4.0 * bvar * bvar + 2.0 * kgrms * kgrms + 20.0 * divrms * divrms + reg)

    def optimize(self, maxiter: int = 700):
        x0 = np.zeros(4)
        return minimize(
            self.objective,
            x0,
            method="Nelder-Mead",
            options={"maxiter": maxiter, "xatol": 2e-5, "fatol": 2e-7},
        )

    def metrics(self, params: np.ndarray) -> RouteCMetrics:
        _, _, _, bmag, kg, div = self.evaluate(params)
        return RouteCMetrics(
            objective=self.objective(params),
            relative_b_std=float(np.std(bmag) / np.mean(bmag)),
            geodesic_curvature_rms=float(np.sqrt(np.mean(kg * kg))),
            surface_divergence_rms=float(np.sqrt(np.mean(div * div))),
        )


def abc_residual(mach: float, alpha: float) -> float:
    return 1.0 - mach * mach - alpha


def exact_ab_alpha(mach: float) -> float:
    return 1.0 - mach * mach


def firehose_margin_fraction(alpha: float) -> float:
    return 1.0 - alpha


if __name__ == "__main__":
    problem = RouteCGeometryProblem()
    baseline = problem.metrics(np.zeros(4))
    result = problem.optimize()
    optimized = problem.metrics(result.x)
    print("baseline", baseline)
    print("params", result.x)
    print("optimized", optimized)
    for m in (0.25, 0.5, 0.7, 0.9):
        a = exact_ab_alpha(m)
        print(m, a, abc_residual(m, a), firehose_margin_fraction(a))
