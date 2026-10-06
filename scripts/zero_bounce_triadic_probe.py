from __future__ import annotations

import math


def trapped_fraction_isotropic(mirror_ratio: float) -> float:
    """Simple adiabatic mirror trapped fraction for an isotropic pitch population.

    mirror_ratio = Bmax / Bmin >= 1.
    f_trapped = sqrt(1 - 1 / mirror_ratio).
    """
    if mirror_ratio < 1.0:
        raise ValueError("mirror_ratio must be >= 1")
    return math.sqrt(max(0.0, 1.0 - 1.0 / mirror_ratio))


def mirror_ratio_for_trapped_fraction(target_fraction: float) -> float:
    if not 0.0 <= target_fraction < 1.0:
        raise ValueError("target_fraction must lie in [0, 1)")
    return 1.0 / (1.0 - target_fraction * target_fraction)


def no_mirror_for_pitch_floor(mirror_ratio: float, minimum_abs_vparallel_over_v: float) -> bool:
    """Sufficient simple-mirror test over |v_parallel|/v >= xi_min.

    Uses R_B * (1 - xi_min^2) < 1.  This is a static adiabatic toy condition,
    not a toroidal-equilibrium or reactor certificate.
    """
    xi = minimum_abs_vparallel_over_v
    if mirror_ratio < 1.0:
        raise ValueError("mirror_ratio must be >= 1")
    if not 0.0 <= xi <= 1.0:
        raise ValueError("minimum_abs_vparallel_over_v must lie in [0, 1]")
    return mirror_ratio * (1.0 - xi * xi) < 1.0


def triadic_phase_count(depth: int) -> int:
    if depth < 1:
        raise ValueError("depth must be >= 1")
    return 3 ** depth


def maximum_phase_quantization_error_radians(depth: int) -> float:
    """Nearest-sector half-width on a C_(3^n) phase grid."""
    return math.pi / triadic_phase_count(depth)


def minimum_triadic_depth_for_phase_error(max_error_radians: float) -> int:
    if max_error_radians <= 0.0:
        raise ValueError("max_error_radians must be positive")
    depth = 1
    while maximum_phase_quantization_error_radians(depth) > max_error_radians:
        depth += 1
    return depth
