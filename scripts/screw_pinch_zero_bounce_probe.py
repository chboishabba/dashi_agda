from __future__ import annotations


def current_density_z(r, Btheta, mu0):
    if r <= 0:
        raise ValueError("r must be positive")
    return Btheta / (mu0 * r)


def pressure_gradient_r(r, Btheta, mu0):
    if r <= 0:
        raise ValueError("r must be positive")
    return -(Btheta * Btheta) / (mu0 * r)


def lorentz_force_r(r, Btheta, mu0):
    return -current_density_z(r, Btheta, mu0) * Btheta


def equilibrium_residual(r, Btheta, mu0):
    return lorentz_force_r(r, Btheta, mu0) - pressure_gradient_r(r, Btheta, mu0)


def mirror_force_parallel(Btheta, Bz):
    # |B| = sqrt(Btheta^2 + Bz^2) is constant on this idealized cylinder.
    return 0.0
