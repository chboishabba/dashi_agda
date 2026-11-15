#!/usr/bin/env python3
"""Exact DASHI Tékum nearest-rounding discovery oracle.

This is a discovery/receipt tool, not semantic authority.  It mirrors the
repository's balanced-ternary, anchor, parser, and exact rational equations
using fractions.Fraction and checks itself against the existing Proposition-5
finite counterexample before producing any census.
"""
from bisect import bisect_left
from fractions import Fraction
from itertools import product

TRITS = (-1, 0, 1)
REGIME = {
    (-1, 1, -1): (5, -244), (-1, 1, 0): (4, -82), (-1, 1, 1): (3, -28),
    (0, -1, -1): (2, -10), (0, -1, 0): (1, -4), (0, -1, 1): (0, -2),
    (0, 0, -1): (0, -1), (0, 0, 0): (0, 0), (0, 0, 1): (0, 1),
    (0, 1, -1): (0, 2), (0, 1, 0): (1, 4), (0, 1, 1): (2, 10),
    (1, -1, -1): (3, 28), (1, -1, 0): (4, 82), (1, -1, 1): (5, 244),
}

def bval(word):
    return sum(d * 3**i for i, d in enumerate(word))

def wrap(value, width):
    modulus = 3**width
    center = (modulus - 1) // 2
    return ((value + center) % modulus) - center

def word_from_value(value, width):
    center = (3**width - 1) // 2
    rank = value + center
    out = []
    for _ in range(width):
        rem = rank % 3
        rank //= 3
        out.append(rem - 1)
    return tuple(out)

def source_center(width):
    return tuple(-1 if i % 2 == 0 else 1 for i in range(width))

def anchor(word):
    width = len(word)
    return word_from_value(
        wrap(abs(bval(word)) - bval(source_center(width)), width), width)

def raw_round(word, target_width):
    anchored = anchor(word)
    dropped = len(word) - target_width
    lower_anchor = anchored[dropped:]
    source_value = wrap(
        bval(lower_anchor) + bval(source_center(target_width)), target_width)
    return word_from_value(source_value, target_width)

def special(word):
    if all(d == -1 for d in word): return "NaR"
    if all(d == 0 for d in word): return "zero"
    if all(d == 1 for d in word): return "infinity"
    return None

def decode(word):
    marker = special(word)
    if marker is not None:
        return marker
    width = len(word)
    if width < 8:
        return None
    msb = tuple(reversed(anchor(word)))
    entry = REGIME.get(msb[:3])
    if entry is None:
        return None
    exponent_count, bias = entry
    payload = msb[3:]
    exponent = bval(tuple(reversed(payload[:exponent_count]))) + bias
    fraction_word = tuple(reversed(payload[exponent_count:]))
    fraction = bval(fraction_word)
    depth = len(fraction_word)
    source_integer = bval(word)
    sign = -1 if source_integer < 0 else (1 if source_integer > 0 else 0)
    value = Fraction(sign * (3**depth + fraction), 3**depth)
    return value * 3**exponent if exponent >= 0 else value / 3**(-exponent)

def ordinary_targets(width):
    out = []
    center = (3**width - 1) // 2
    for code in range(-center, center + 1):
        word = word_from_value(code, width)
        value = decode(word)
        if isinstance(value, Fraction):
            out.append((value, word, code))
    return sorted(out, key=lambda row: row[0])

def nearest_set(value, targets):
    values = [row[0] for row in targets]
    i = bisect_left(values, value)
    adjacent = [targets[j] for j in (i - 1, i) if 0 <= j < len(targets)]
    minimum = min(abs(value - row[0]) for row in adjacent)
    return [row for row in adjacent if abs(value - row[0]) == minimum]

def canonical_nearest(value, targets):
    nearest = nearest_set(value, targets)
    # DASHI fallback tie rule: lower source balanced-integer code.  This is
    # intrinsic to the target representation and independent of enumeration.
    return min(nearest, key=lambda row: row[2]), nearest

def validate_known_counterexample():
    source = (1,-1,1,-1,1,-1,1,0,-1,1)
    target = (1,-1,1,-1,1,0,-1,1)
    competitor = (0,-1,1,-1,1,0,-1,1)
    assert decode(source) == Fraction(1094, 2187)
    assert raw_round(source, 8) == target
    assert decode(target) == Fraction(122, 243)
    assert decode(competitor) == Fraction(364, 729)
    assert abs(decode(source)-decode(competitor)) == Fraction(2,2187)
    assert abs(decode(source)-decode(target)) == Fraction(4,2187)

def correction_census(source_width, target_width, targets):
    center = (3**source_width - 1) // 2
    ordinary = ties = raw_special = raw_ordinary = raw_not_nearest = 0
    max_abs_displacement = -1
    max_row = None
    for code in range(-center, center + 1):
        word = word_from_value(code, source_width)
        value = decode(word)
        if not isinstance(value, Fraction):
            continue
        ordinary += 1
        chosen, nearest = canonical_nearest(value, targets)
        ties += len(nearest) > 1
        raw = raw_round(word, target_width)
        raw_value = decode(raw)
        if not isinstance(raw_value, Fraction):
            raw_special += 1
            continue
        raw_ordinary += 1
        displacement = chosen[2] - bval(raw)
        raw_not_nearest += all(raw != candidate[1] for candidate in nearest)
        if abs(displacement) > max_abs_displacement:
            max_abs_displacement = abs(displacement)
            max_row = (code, word, value, raw, raw_value, chosen, displacement)
    return {
        "ordinary_sources": ordinary,
        "ties": ties,
        "raw_special": raw_special,
        "raw_ordinary": raw_ordinary,
        "raw_not_nearest": raw_not_nearest,
        "max_abs_displacement": max_abs_displacement,
        "max_displacement_witness": max_row,
    }

def first_no_double_rounding_mismatch(targets10, targets8):
    round10to8 = {
        row[1]: canonical_nearest(row[0], targets8)[0] for row in targets10
    }
    center12 = (3**12 - 1) // 2
    for code in range(-center12, center12 + 1):
        word = word_from_value(code, 12)
        value = decode(word)
        if not isinstance(value, Fraction):
            continue
        intermediate, nearest10 = canonical_nearest(value, targets10)
        two_stage = round10to8[intermediate[1]]
        direct, nearest8 = canonical_nearest(value, targets8)
        if two_stage[1] != direct[1]:
            return {
                "source_code": code,
                "source_word": word,
                "source_value": value,
                "intermediate": intermediate,
                "intermediate_nearest_set": nearest10,
                "two_stage_final": two_stage,
                "intermediate_to_8_nearest_set": nearest_set(intermediate[0], targets8),
                "direct_final": direct,
                "direct_nearest_set": nearest8,
            }
    return None

def main():
    validate_known_counterexample()
    targets8 = ordinary_targets(8)
    targets10 = ordinary_targets(10)
    c108 = correction_census(10, 8, targets8)
    c1210 = correction_census(12, 10, targets10)
    mismatch = first_no_double_rounding_mismatch(targets10, targets8)
    print("10->8", c108)
    print("12->10", c1210)
    print("first 12->10->8 mismatch", mismatch)
    assert len(targets8) == 6558
    assert len(targets10) == 59046
    assert c108["ordinary_sources"] == 59046
    assert c108["ties"] == 708
    assert c108["raw_special"] == 24
    assert c108["raw_not_nearest"] == 29875
    assert c108["max_abs_displacement"] == 6558
    assert c1210["ordinary_sources"] == 531438
    assert c1210["ties"] == 712
    assert c1210["raw_special"] == 24
    assert c1210["raw_not_nearest"] == 266073
    assert c1210["max_abs_displacement"] == 59046
    assert mismatch is not None
    assert mismatch["source_code"] == -265591

if __name__ == "__main__":
    main()
