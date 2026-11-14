from __future__ import annotations

import cmath
import math
from typing import Iterable


def phase_filter(sectors: int, harmonic: int) -> complex:
    """Equal C_N phase average of the harmonic exp(i*m*alpha)."""
    if sectors <= 0:
        raise ValueError("sectors must be positive")
    return sum(
        cmath.exp(2j * math.pi * harmonic * j / sectors)
        for j in range(sectors)
    ) / sectors


def first_surviving_harmonic(sectors: int, harmonics: Iterable[int]):
    """Return the first positive harmonic not annihilated by the C_N projector."""
    if sectors <= 0:
        raise ValueError("sectors must be positive")
    for harmonic in harmonics:
        if harmonic % sectors == 0:
            return harmonic
    return None


def pure_triadic_sector_count(depth: int) -> int:
    if depth < 1:
        raise ValueError("depth must be >= 1")
    return 3 ** depth


def projector_residual_bound_from_coefficients(sectors: int, coefficients):
    """Triangle bound after exact C_N harmonic filtering.

    `coefficients[m]` is a magnitude bound for angular Fourier mode m.
    Only multiples of N survive the equal-phase average.
    """
    if sectors <= 0:
        raise ValueError("sectors must be positive")
    return sum(abs(value) for m, value in coefficients.items() if m % sectors == 0)
