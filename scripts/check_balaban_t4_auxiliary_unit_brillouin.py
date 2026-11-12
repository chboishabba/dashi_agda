#!/usr/bin/env python3
"""Exact-rational, source-independent check of normalized 4D Brillouin
free-Wilson auxiliary bounds. Not a physical beta-integral certificate.
Source owners: BalabanClayT4GeneratedBrillouinGridExact,
BalabanClayT4RefinedSineSquareRegularBoxesExact and
BalabanClayT4FourAuxiliaryWilsonPropagatorBoxesExact.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product

CATEGORIES = ("negativeOuter", "negativeInner", "positiveInner", "positiveOuter")
OUTER = {"negativeOuter", "positiveOuter"}
FOUR_SINE_SQUARE_FLOOR = Q(7569, 4096)
CELL_VOLUME = Q(1, 2) ** 4
BRILLOUIN_PROBABILITY_DENSITY = Q(1, 16)


def original_grid():
    return list(product(CATEGORIES, repeat=4))


def certified_interval(cell):
    m = sum(c in OUTER for c in cell)
    if m == 0:
        return None  # singular infrared group: no licensed reciprocal
    denominator_low = m * FOUR_SINE_SQUARE_FLOOR
    denominator_high = Q(16, 1)  # four components, each at most four
    assert 0 < denominator_low <= denominator_high
    return m, Q(1, 1) / denominator_high, Q(1, 1) / denominator_low


def main():
    cells = original_grid()
    assert len(cells) == 256
    counts = Counter(sum(c in OUTER for c in x) for x in cells)
    assert counts == {0: 16, 1: 64, 2: 96, 3: 64, 4: 16}
    assert CELL_VOLUME == Q(1, 16)
    assert sum(counts.values()) * CELL_VOLUME == 16
    normalized_cell_mass = CELL_VOLUME * BRILLOUIN_PROBABILITY_DENSITY
    assert normalized_cell_mass == Q(1, 256)
    assert normalized_cell_mass * len(cells) == 1
    assert counts[0] * normalized_cell_mass == Q(1, 16)

    regular = [certified_interval(c) for c in cells]
    regular = [c for c in regular if c is not None]
    assert len(regular) == 240
    assert sum(normalized_cell_mass for _ in regular) == Q(15, 16)

    lower = sum((v[1] * normalized_cell_mass for v in regular), Q(0))
    upper = sum((v[2] * normalized_cell_mass for v in regular), Q(0))
    assert lower == Q(15, 256)
    assert upper == Q(6592, 22707)
    assert lower < upper

    four_weight_upper = sum(
        (Q(counts[m], 16) * Q(4096, 7569 * m)
         for m in range(1, 5)), Q(0))
    four_weight_lower = sum(
        (Q(counts[m], 16) * Q(1, 16)
         for m in range(1, 5)), Q(0))
    assert four_weight_lower == Q(15, 16)
    assert four_weight_upper == Q(105472, 22707)
    assert lower == four_weight_lower / 16
    assert upper == four_weight_upper / 16
    assert Q(1) / 16 * 16 == 1

    # A full integral enclosure requires a true physical pointwise
    # enclosure for each cell, and an appropriate integration theorem.
    # Nothing here encloses the 16-cell infrared integral, shifted
    # propagators or the interacting Wilson+ghost+Haar beta kernel.
    print("PASS: 256/256 source-grid cells counted, 240 regular")
    print("PASS: all 4 orbit populations and 1/256 unit-volume Jacobian")
    print("PASS: original unnormalized four-orbit lower", four_weight_lower)
    print("PASS: original unnormalized four-orbit upper", four_weight_upper)
    print("PASS: unit-mass regular free-Wilson lower", lower)
    print("PASS: unit-mass regular free-Wilson upper", upper)
    print("OPEN: physical sine membership, infrared, shifted, and beta scalar")


if __name__ == "__main__":
    main()
