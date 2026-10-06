from __future__ import annotations
from typing import Iterable, Mapping


def greenwald_density_m3(plasma_current_ma: float, minor_radius_m: float) -> float:
    """Greenwald density n_G in m^-3 from Ip[MA] and a[m].

    n_G [10^20 m^-3] = Ip[MA] / (pi a^2).
    """
    import math
    if minor_radius_m <= 0:
        raise ValueError("minor_radius_m must be positive")
    if plasma_current_ma < 0:
        raise ValueError("plasma_current_ma must be non-negative")
    return (plasma_current_ma / (math.pi * minor_radius_m**2)) * 1e20


def greenwald_fraction(
    line_averaged_electron_density_m3: float,
    plasma_current_ma: float,
    minor_radius_m: float,
) -> float:
    n_g = greenwald_density_m3(plasma_current_ma, minor_radius_m)
    if n_g == 0:
        raise ValueError("Greenwald fraction undefined at zero plasma current")
    return line_averaged_electron_density_m3 / n_g


def net_electric_mw(
    gross_electric_mw: float,
    recirculating_loads_mw: Iterable[float],
) -> float:
    return gross_electric_mw - sum(recirculating_loads_mw)


def weakly_dominates(
    left: Mapping[str, float],
    right: Mapping[str, float],
    axes: Mapping[str, str],
) -> bool:
    for key, sense in axes.items():
        if sense == "min":
            if left[key] > right[key]:
                return False
        elif sense == "max":
            if left[key] < right[key]:
                return False
        else:
            raise ValueError(f"axis {key!r} must be 'min' or 'max'")
    return True


def strictly_dominates(
    left: Mapping[str, float],
    right: Mapping[str, float],
    axes: Mapping[str, str],
) -> bool:
    if not weakly_dominates(left, right, axes):
        return False
    return any(
        left[key] < right[key] if sense == "min" else left[key] > right[key]
        for key, sense in axes.items()
    )
