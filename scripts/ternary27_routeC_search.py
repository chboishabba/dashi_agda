from __future__ import annotations

import numpy as np
from scipy.optimize import minimize


def c3_basis(theta: np.ndarray, zeta: np.ndarray):
    """Nine real harmonics invariant under zeta -> zeta + 2*pi/3."""
    return np.stack([
        np.ones_like(theta),
        np.cos(theta), np.sin(theta),
        np.cos(3*zeta), np.sin(3*zeta),
        np.cos(theta-3*zeta), np.sin(theta-3*zeta),
        np.cos(theta+3*zeta), np.sin(theta+3*zeta),
    ], axis=-1)


def c3_basis_dtheta(theta: np.ndarray, zeta: np.ndarray):
    return np.stack([
        np.zeros_like(theta),
        -np.sin(theta), np.cos(theta),
        np.zeros_like(theta), np.zeros_like(theta),
        -np.sin(theta-3*zeta), np.cos(theta-3*zeta),
        -np.sin(theta+3*zeta), np.cos(theta+3*zeta),
    ], axis=-1)


def c3_basis_dzeta(theta: np.ndarray, zeta: np.ndarray):
    return np.stack([
        np.zeros_like(theta),
        np.zeros_like(theta), np.zeros_like(theta),
        -3*np.sin(3*zeta), 3*np.cos(3*zeta),
        3*np.sin(theta-3*zeta), -3*np.cos(theta-3*zeta),
        -3*np.sin(theta+3*zeta), 3*np.cos(theta+3*zeta),
    ], axis=-1)


def periodic_derivative(f, axis, h):
    return (np.roll(f, -1, axis=axis) - np.roll(f, 1, axis=axis))/(2*h)


class Ternary27RouteC:
    """Three physical channels x nine C3-compatible harmonics = 27 coordinates.

    Channels are radial surface shaping, vertical surface shaping, and periodic
    stream-function correction.  The literal 27 count is only a search chart;
    no exceptional-algebra semantics are assumed.
    """

    def __init__(self, nth=20, nz=24, R0=3.0, a0=1.0, iota0=0.42):
        self.nth, self.nz = nth, nz
        self.R0, self.a0, self.iota0 = R0, a0, iota0
        self.theta = np.linspace(0, 2*np.pi, nth, endpoint=False)
        self.zeta = np.linspace(0, 2*np.pi, nz, endpoint=False)
        self.TH, self.ZE = np.meshgrid(self.theta, self.zeta, indexing="ij")
        self.dth, self.dze = 2*np.pi/nth, 2*np.pi/nz
        self.B = c3_basis(self.TH, self.ZE)
        self.Bt = c3_basis_dtheta(self.TH, self.ZE)
        self.Bz = c3_basis_dzeta(self.TH, self.ZE)
        self.free_idx = [i for i in range(27) if i not in (0, 9, 18)]

    def embed(self, free):
        coeff = np.zeros(27)
        coeff[self.free_idx] = free
        return coeff

    def evaluate(self, coeff):
        cr, cz, cs = coeff[:9], coeff[9:18], coeff[18:]
        rho = self.a0*(1 + np.tensordot(self.B, cr, axes=([-1], [0])))
        zoff = self.a0*np.tensordot(self.B, cz, axes=([-1], [0]))
        RR = self.R0 + rho*np.cos(self.TH)
        ZZ = rho*np.sin(self.TH) + zoff
        r = np.stack([RR*np.cos(self.ZE), RR*np.sin(self.ZE), ZZ], axis=-1)
        e1 = periodic_derivative(r, 0, self.dth)
        e2 = periodic_derivative(r, 1, self.dze)
        cross = np.cross(e1, e2)
        sqrtg = np.linalg.norm(cross, axis=-1)
        normal = cross/sqrtg[..., None]

        dchi_t = 1 + np.tensordot(self.Bt, cs, axes=([-1], [0]))
        dchi_z = -self.iota0 + np.tensordot(self.Bz, cs, axes=([-1], [0]))
        Bth = dchi_z/sqrtg
        Bze = -dchi_t/sqrtg
        Bvec = Bth[..., None]*e1 + Bze[..., None]*e2
        Bmag = np.linalg.norm(Bvec, axis=-1)
        bhat = Bvec/Bmag[..., None]
        bt, bz = Bth/Bmag, Bze/Bmag
        kappa = bt[..., None]*periodic_derivative(bhat, 0, self.dth) + bz[..., None]*periodic_derivative(bhat, 1, self.dze)
        q = np.cross(normal, bhat)
        q /= np.linalg.norm(q, axis=-1)[..., None]
        kg = np.sum(kappa*q, axis=-1)
        div = (periodic_derivative(sqrtg*Bth, 0, self.dth) + periodic_derivative(sqrtg*Bze, 1, self.dze))/sqrtg
        return r, Bmag, kg, div, float(np.min(rho))

    def metrics(self, coeff):
        _, Bmag, kg, div, minrho = self.evaluate(coeff)
        return {
            "relative_B_spread": float(np.std(Bmag)/np.mean(Bmag)),
            "geodesic_curvature_rms": float(np.sqrt(np.mean(kg*kg))),
            "surface_divergence_rms": float(np.sqrt(np.mean(div*div))),
            "minimum_minor_radius": minrho,
            "coefficient_norm": float(np.linalg.norm(coeff)),
        }

    def objective(self, free, delta_c):
        coeff = self.embed(free)
        m = self.metrics(coeff)
        barrier = 0.0 if m["minimum_minor_radius"] > 0.35 else 300*(0.35-m["minimum_minor_radius"])**2
        return (20*m["relative_B_spread"]**2
                + (0.5 + 4*delta_c)*m["geodesic_curvature_rms"]**2
                + 50*m["surface_divergence_rms"]**2
                + 0.02*m["coefficient_norm"]**2 + barrier)

    def continuation(self, levels=(0.0, 0.2, 0.4, 0.6, 0.8, 1.0), maxiter=120):
        free = np.zeros(len(self.free_idx))
        rows = []
        for delta_c in levels:
            result = minimize(lambda x: self.objective(x, delta_c), free,
                              method="L-BFGS-B", bounds=[(-0.18, 0.18)]*len(free),
                              options={"maxiter": maxiter, "ftol": 1e-9})
            free = result.x
            coeff = self.embed(free)
            rows.append((delta_c, result.fun, self.metrics(coeff), coeff.copy()))
        return rows


if __name__ == "__main__":
    problem = Ternary27RouteC()
    for level, value, metrics, _ in problem.continuation():
        print(level, value, metrics)
