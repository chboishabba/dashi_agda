from __future__ import annotations

import numpy as np


def periodic_derivative(f: np.ndarray, axis: int, h: float) -> np.ndarray:
    return (np.roll(f, -1, axis=axis) - np.roll(f, 1, axis=axis)) / (2.0 * h)


def shaped_torus(theta: np.ndarray, zeta: np.ndarray, R0=3.0, a=1.0,
                 epsilon=0.10, nfp=3):
    phase = theta - nfp * zeta
    rho = a * (1.0 + epsilon * np.cos(phase))
    R = R0 + rho * np.cos(theta)
    Z = rho * np.sin(theta)
    return np.stack([R * np.cos(zeta), R * np.sin(zeta), Z], axis=-1)


class WindingSurfaceInverse:
    """Normalized REGCOIL/NESCOIL-style current-potential probe.

    The probe solves only the external current-sheet inverse for a target normal
    field on the plasma boundary.  It does not reproduce the complete finite-beta
    interior field and does not assign engineering current units.
    """

    def __init__(self, nt=12, nz=15, R0=3.0, a=1.0, aw=1.35,
                 epsilon=0.10, nfp=3):
        self.nt, self.nz = nt, nz
        self.R0, self.a, self.aw = R0, a, aw
        self.epsilon, self.nfp = epsilon, nfp
        self.theta = np.linspace(0.0, 2.0 * np.pi, nt, endpoint=False)
        self.zeta = np.linspace(0.0, 2.0 * np.pi, nz, endpoint=False)
        self.TH, self.ZE = np.meshgrid(self.theta, self.zeta, indexing="ij")
        self.dth = 2.0 * np.pi / nt
        self.dze = 2.0 * np.pi / nz

        self.plasma = shaped_torus(self.TH, self.ZE, R0, a, epsilon, nfp)
        self.winding = shaped_torus(self.TH, self.ZE, R0, aw, 0.75 * epsilon, nfp)
        self.p_rt, self.p_rz, self.p_jac, self.p_normal = self._surface_geometry(self.plasma)
        self.w_rt, self.w_rz, self.w_jac, self.w_normal = self._surface_geometry(self.winding)
        self.modes = self._modes()
        self.target = self._target_normal_field()
        self.matrix = self._biot_savart_matrix()

    def _surface_geometry(self, r):
        rt = periodic_derivative(r, 0, self.dth)
        rz = periodic_derivative(r, 1, self.dze)
        cross = np.cross(rt, rz)
        jac = np.linalg.norm(cross, axis=-1)
        normal = cross / jac[..., None]
        return rt, rz, jac, normal

    def _modes(self):
        modes = []
        for m in (0, 1, 2):
            for n in (1, 2):
                modes.append(("cos", m, n))
                modes.append(("sin", m, n))
        for m in (1, 2, 3):
            modes.append(("cos", m, 0))
            modes.append(("sin", m, 0))
        return modes

    def _target_normal_field(self):
        rp = self.plasma
        Rxy = np.sqrt(rp[..., 0] ** 2 + rp[..., 1] ** 2)
        ephi = np.stack([-rp[..., 1] / Rxy,
                         rp[..., 0] / Rxy,
                         np.zeros_like(Rxy)], axis=-1)
        base = (self.R0 / Rxy)[..., None] * ephi
        leakage = np.sum(base * self.p_normal, axis=-1)
        return -leakage.reshape(-1)

    def _current_from_mode(self, mode):
        kind, m, n = mode
        arg = m * self.TH - n * self.nfp * self.ZE
        if kind == "cos":
            pt = -m * np.sin(arg)
            pz = n * self.nfp * np.sin(arg)
        else:
            pt = m * np.cos(arg)
            pz = -n * self.nfp * np.cos(arg)

        gtt = np.sum(self.w_rt * self.w_rt, axis=-1)
        gtz = np.sum(self.w_rt * self.w_rz, axis=-1)
        gzz = np.sum(self.w_rz * self.w_rz, axis=-1)
        detg = gtt * gzz - gtz * gtz
        git = gzz / detg
        giz = -gtz / detg
        gzz_inv = gtt / detg
        grad_t = git * pt + giz * pz
        grad_z = giz * pt + gzz_inv * pz
        grad = grad_t[..., None] * self.w_rt + grad_z[..., None] * self.w_rz
        return np.cross(self.w_normal, grad)

    def _biot_savart_matrix(self, softening=0.035):
        P = self.plasma.reshape(-1, 3)
        PN = self.p_normal.reshape(-1, 3)
        W = self.winding.reshape(-1, 3)
        area = (self.w_jac * self.dth * self.dze).reshape(-1)
        A = np.zeros((P.shape[0], len(self.modes)))
        for j, mode in enumerate(self.modes):
            K = self._current_from_mode(mode).reshape(-1, 3)
            dR = P[:, None, :] - W[None, :, :]
            r2 = np.sum(dR * dR, axis=-1) + softening ** 2
            dB = np.cross(K[None, :, :], dR) * area[None, :, None] / (r2 ** 1.5)[..., None]
            B = np.sum(dB, axis=1)
            A[:, j] = np.sum(B * PN, axis=-1)
        return A

    def solve(self, lam=0.1):
        A = self.matrix
        c = np.linalg.solve(A.T @ A + lam * np.eye(A.shape[1]), A.T @ self.target)
        prediction = A @ c
        residual = prediction - self.target
        rms = float(np.sqrt(np.mean(residual * residual)))
        target_rms = float(np.sqrt(np.mean(self.target * self.target)))
        return {
            "lambda": float(lam),
            "coefficients": c,
            "absolute_rms": rms,
            "relative_rms": rms / target_rms if target_rms > 0.0 else 0.0,
            "coefficient_norm": float(np.linalg.norm(c)),
        }

    def current_potential(self, coefficients):
        Phi = np.zeros_like(self.TH)
        for mode, value in zip(self.modes, coefficients):
            kind, m, n = mode
            arg = m * self.TH - n * self.nfp * self.ZE
            Phi += value * (np.cos(arg) if kind == "cos" else np.sin(arg))
        return Phi


if __name__ == "__main__":
    problem = WindingSurfaceInverse()
    for lam in np.logspace(-8, -1, 8):
        print(problem.solve(float(lam)))
