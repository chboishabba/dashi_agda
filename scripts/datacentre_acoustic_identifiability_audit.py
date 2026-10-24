#!/usr/bin/env python3
"""Illustrative acoustics audit: identical dBA can hide different tonal spectra.

No site data, human outcome, or acoustic safety claim is implied.
Python 3 standard library only.
"""
from dataclasses import dataclass
from math import log10, sqrt


@dataclass(frozen=True)
class Tone:
    hz: float
    db_spl: float


def a_weight_db(hz: float) -> float:
    """IEC-style analog frequency-response approximation, 0 dB at 1 kHz."""
    if hz <= 0:
        raise ValueError("frequency must be positive")
    f2 = hz * hz
    ra = (12194.0**2 * f2**2) / (
        (f2 + 20.6**2) *
        sqrt((f2 + 107.7**2) * (f2 + 737.9**2)) *
        (f2 + 12194.0**2)
    )
    return 20 * log10(ra) + 2.0


def combined_level_db(levels):
    levels = list(levels)
    if not levels:
        raise ValueError("at least one tone is required")
    return 10 * log10(sum(10**(v/10) for v in levels))


def a_weighted_level(tones):
    return combined_level_db(t.db_spl + a_weight_db(t.hz) for t in tones)


def flat_level(tones):
    return combined_level_db(t.db_spl for t in tones)


def claimed_percent_to_db(percent_increase: float, ratio_kind: str):
    """A percent comparison needs a named amplitude or power quantity."""
    if percent_increase < 0:
        raise ValueError("negative percent increase not supported")
    ratio = 1 + percent_increase / 100.0
    if ratio_kind == "pressure_amplitude":
        return 20 * log10(ratio)
    if ratio_kind == "acoustic_power":
        return 10 * log10(ratio)
    raise ValueError("specify pressure_amplitude or acoustic_power")


def same_la_example(la_target=35.0):
    low = Tone(31.5, la_target - a_weight_db(31.5))
    high = Tone(125.0, la_target - a_weight_db(125.0))
    assert abs(a_weighted_level([low]) - la_target) < 1e-8
    assert abs(a_weighted_level([high]) - la_target) < 1e-8
    assert abs(flat_level([low]) - flat_level([high])) > 20.0
    return low, high


if __name__ == "__main__":
    low, high = same_la_example()
    print("Two idealised pure tones at identical 35 dB(A), NOT measured sites:")
    for tone in [low, high]:
        print(f"{tone.hz:6.1f} Hz | A {a_weight_db(tone.hz):6.2f} dB | "
              f"flat {tone.db_spl:6.2f} dB SPL | LA {a_weighted_level([tone]):.2f} dBA")
    print(f"Unweighted SPL difference: {low.db_spl-high.db_spl:.2f} dB")
    print("25,000% above baseline maps to different decibels by quantity:")
    print(f"pressure amplitude: {claimed_percent_to_db(25000, 'pressure_amplitude'):.2f} dB")
    print(f"acoustic power: {claimed_percent_to_db(25000, 'acoustic_power'):.2f} dB")
    print("Equal LA is NOT equal spectra; no biological inference follows.")
