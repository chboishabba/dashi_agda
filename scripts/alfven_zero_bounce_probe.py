from __future__ import annotations

import math
import numpy as np


def field_and_velocity(z, t, B0, amp, k, rho, mu0):
    vA = B0 / math.sqrt(mu0 * rho)
    omega = k * vA
    phase = k * z - omega * t
    b = np.array([amp * math.cos(phase), amp * math.sin(phase), 0.0])
    B = b + np.array([0.0, 0.0, B0])
    u = -b / math.sqrt(mu0 * rho)
    return B, u, omega


def mirror_force_parallel(B0, amp, k, rho):
    # |B| = sqrt(B0^2 + amp^2) exactly for this circularly-polarized seed.
    # Hence grad_parallel |B| = 0 and the adiabatic magnetic-mirror force vanishes.
    return 0.0


def curvature_magnitude(B0, amp, k):
    # For b-hat = B/|B| with z-dependent transverse phase only,
    # |(b-hat . grad)b-hat| = |k amp B0| / (B0^2 + amp^2).
    return abs(k * amp * B0 / (B0 * B0 + amp * amp))


def check_exact_ideal_mhd(B0, amp, k, rho, mu0):
    zs = np.linspace(0.0, 2.0 * math.pi / max(abs(k), 1e-12), 41)
    ts = np.linspace(0.0, 1e-5, 7)
    target_Bmag2 = B0 * B0 + amp * amp
    max_Bmag2_error = 0.0
    max_momentum_residual = 0.0
    max_induction_residual = 0.0
    vA = B0 / math.sqrt(mu0 * rho)
    omega = k * vA

    for z in zs:
        for t in ts:
            phase = k * z - omega * t
            B = np.array([amp * math.cos(phase), amp * math.sin(phase), B0])
            max_Bmag2_error = max(
                max_Bmag2_error,
                abs(float(B @ B) - target_Bmag2),
            )

            du_dt = np.array([
                -amp * omega * math.sin(phase) / math.sqrt(mu0 * rho),
                 amp * omega * math.cos(phase) / math.sqrt(mu0 * rho),
                 0.0,
            ])
            curlB = np.array([
                -amp * k * math.cos(phase),
                -amp * k * math.sin(phase),
                0.0,
            ])
            lorentz_per_mass = np.cross(curlB, B) / (mu0 * rho)
            max_momentum_residual = max(
                max_momentum_residual,
                float(np.linalg.norm(du_dt - lorentz_per_mass)),
            )

            dB_dt = np.array([
                amp * omega * math.sin(phase),
                -amp * omega * math.cos(phase),
                0.0,
            ])
            dF_x_dz = amp * B0 * k * math.cos(phase) / math.sqrt(mu0 * rho)
            dF_y_dz = amp * B0 * k * math.sin(phase) / math.sqrt(mu0 * rho)
            curl_u_cross_B = np.array([-dF_y_dz, dF_x_dz, 0.0])
            max_induction_residual = max(
                max_induction_residual,
                float(np.linalg.norm(dB_dt - curl_u_cross_B)),
            )

    return {
        "max_Bmag2_error": max_Bmag2_error,
        "max_momentum_residual": max_momentum_residual,
        "max_induction_residual": max_induction_residual,
    }
