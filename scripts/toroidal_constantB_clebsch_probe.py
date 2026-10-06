from __future__ import annotations
import math
import numpy as np


def h_zeta(R0: float, r: float, theta: float) -> float:
    return R0 + r * math.cos(theta)


def field_components(R0: float, r: float, theta: float, B0: float, C: float):
    h = h_zeta(R0, r, theta)
    if abs(C) >= abs(B0) * (R0 - r):
        raise ValueError("require |C| < |B0| (R0-r) for real B_zeta on whole surface")
    Btheta = C / h
    Bzeta = math.sqrt(B0 * B0 - Btheta * Btheta)
    return 0.0, Btheta, Bzeta


def magnitude(R0: float, r: float, theta: float, B0: float, C: float) -> float:
    _, bt, bz = field_components(R0, r, theta, B0, C)
    return math.sqrt(bt * bt + bz * bz)


def divergence_residual(R0: float, r: float, theta: float, B0: float, C: float) -> float:
    # Axisymmetric Br=0: div B = 1/(r h) d_theta(h Btheta), while h Btheta=C.
    return 0.0


def curl_components(R0: float, r: float, theta: float, B0: float, C: float, mu0: float = 1.0):
    h = h_zeta(R0, r, theta)
    _, bt, bz = field_components(R0, r, theta, B0, C)
    hp = -r * math.sin(theta)
    q = math.sqrt(B0 * B0 * h * h - C * C)  # q = h Bzeta
    q_theta = (B0 * B0 * h * hp) / q
    Jr = q_theta / (mu0 * r * h)
    hr = math.cos(theta)
    q_r = (B0 * B0 * h * hr) / q
    Jtheta = -q_r / (mu0 * h)
    # d_r(r C/h)=C R0/h^2
    Jzeta = (C * R0 / (h * h)) / (mu0 * r)
    return Jr, Jtheta, Jzeta


def lorentz_components(R0: float, r: float, theta: float, B0: float, C: float, mu0: float = 1.0):
    Jr, Jt, Jz = curl_components(R0, r, theta, B0, C, mu0)
    _, Bt, Bz = field_components(R0, r, theta, B0, C)
    return Jt * Bz - Jz * Bt, -Jr * Bz, Jr * Bt


def fieldline_one_poloidal_turn(R0: float = 3.0, r: float = 1.0, B0: float = 1.0,
                                 C: float = 1.0, samples: int = 4097):
    theta = np.linspace(0.0, 2.0 * math.pi, samples)
    bzeta = np.array([field_components(R0, r, float(t), B0, C)[2] for t in theta])
    dzeta_dtheta = r * bzeta / C
    zeta = np.zeros_like(theta)
    dtheta = theta[1] - theta[0]
    zeta[1:] = np.cumsum(0.5 * (dzeta_dtheta[1:] + dzeta_dtheta[:-1]) * dtheta)

    x = np.stack([
        (R0 + r * np.cos(theta)) * np.cos(zeta),
        (R0 + r * np.cos(theta)) * np.sin(zeta),
        r * np.sin(theta),
    ], axis=1)

    d1 = np.gradient(x, theta, axis=0, edge_order=2)
    speed = np.linalg.norm(d1, axis=1)
    tangent = d1 / speed[:, None]
    dT = np.gradient(tangent, theta, axis=0, edge_order=2)
    kappa = dT / speed[:, None]
    drift = np.cross(tangent, kappa)
    er = np.stack([
        np.cos(theta) * np.cos(zeta),
        np.cos(theta) * np.sin(zeta),
        np.sin(theta),
    ], axis=1)
    radial = np.einsum("ij,ij->i", drift, er)
    avg = np.trapezoid(radial * speed, theta) / np.trapezoid(speed, theta)
    rms = math.sqrt(np.trapezoid(radial * radial * speed, theta) / np.trapezoid(speed, theta))
    return theta, radial, avg, rms


def phase_project(values, sectors: int):
    values = np.asarray(values, dtype=float)
    count = len(values)
    if count % sectors:
        raise ValueError("sample count must be divisible by sectors")
    shift = count // sectors
    projected = np.zeros_like(values)
    for j in range(sectors):
        projected += np.roll(values, j * shift)
    return projected / sectors
