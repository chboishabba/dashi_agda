from __future__ import annotations
import math
from typing import Iterable


def control_frequency_lower_bound(required_phase_advance_rad: float, turning_time_s: float) -> float:
    """Minimum angular control rate needed to advance the field phase before a nominal mirror turn."""
    if required_phase_advance_rad < 0:
        raise ValueError("required_phase_advance_rad must be non-negative")
    if turning_time_s <= 0:
        raise ValueError("turning_time_s must be positive")
    return required_phase_advance_rad / turning_time_s


def adiabatic_control_frequency_upper_bound(cyclotron_angular_frequency: float, max_fraction: float) -> float:
    """Declared guiding-centre/adiabatic ceiling omega_control <= max_fraction * Omega_c."""
    if cyclotron_angular_frequency <= 0:
        raise ValueError("cyclotron_angular_frequency must be positive")
    if not 0 < max_fraction < 1:
        raise ValueError("max_fraction must lie in (0,1)")
    return max_fraction * cyclotron_angular_frequency


def detrapping_window_exists(lower_bound: float, upper_bound: float) -> bool:
    """Whether a non-empty control-rate window exists between turning and adiabatic constraints."""
    return 0 <= lower_bound < upper_bound


def minimum_triadic_depth_for_turning_time(control_angular_frequency: float, turning_time_s: float) -> int:
    """Smallest n>=1 such that one C_(3^n) phase-sector update fits inside turning_time_s."""
    if control_angular_frequency <= 0 or turning_time_s <= 0:
        raise ValueError("frequency and time must be positive")
    depth = 1
    cycle_time = 2 * math.pi / control_angular_frequency
    while cycle_time / (3 ** depth) >= turning_time_s:
        depth += 1
    return depth


def resonance_clear(
    control_angular_frequency: float,
    resonance_fundamentals: Iterable[float],
    relative_margin: float = 0.05,
    max_harmonic: int = 3,
) -> bool:
    """Reject a control rate lying within a declared margin of low-order harmonics.

    This is a screening predicate only; it is not a nonlinear resonance theorem.
    """
    if control_angular_frequency <= 0:
        raise ValueError("control_angular_frequency must be positive")
    if not 0 <= relative_margin < 1:
        raise ValueError("relative_margin must lie in [0,1)")
    if max_harmonic < 1:
        raise ValueError("max_harmonic must be >=1")
    for fundamental in resonance_fundamentals:
        if fundamental <= 0:
            raise ValueError("resonance fundamentals must be positive")
        for harmonic in range(1, max_harmonic + 1):
            target = harmonic * fundamental
            if abs(control_angular_frequency - target) <= relative_margin * target:
                return False
    return True
