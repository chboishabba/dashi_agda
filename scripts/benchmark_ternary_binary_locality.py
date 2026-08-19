#!/usr/bin/env python3
"""Exact finite benchmark for native T^9 operations under binary encodings.

This is deliberately not a hardware-performance theorem.  It compares two
explicit lossless binary representations of the same 3^9 state set:

1. compact rank codec: base-3 rank 0..19682 stored in 15 bits;
2. structured codec: each trit gets the explicit two-bit code
      -1 -> 00, 0 -> 01, +1 -> 10
   used by TernaryNativeMinimalityExact, for 18 bits total.

The benchmark exhaustively conjugates local ternary antipode through the compact
rank codec and measures binary Hamming mutation.  The structured codec retains
the local product geometry by construction, but spends three extra bits.

No claim is made that every 15-bit binary embedding has these locality costs or
that Hamming mutation equals transistor/runtime complexity.
"""

from __future__ import annotations

from itertools import product

TRITS = (0, 1, 2)  # semantic -1, 0, +1
N = 3**9


def rank3(digits: tuple[int, ...]) -> int:
    return sum(digit * (3**i) for i, digit in enumerate(digits))


def antipode_digit(digit: int) -> int:
    return 2 - digit


def flip_coordinate(digits: tuple[int, ...], coordinate: int) -> tuple[int, ...]:
    out = list(digits)
    out[coordinate] = antipode_digit(out[coordinate])
    return tuple(out)


def hamming_int(left: int, right: int) -> int:
    return (left ^ right).bit_count()


def rotate90(digits: tuple[int, ...]) -> tuple[int, ...]:
    """Clockwise 90-degree rotation of a row-major 3x3 ternary sheet."""
    out = [0] * 9
    for row in range(3):
        for column in range(3):
            out[row * 3 + column] = digits[(2 - column) * 3 + row]
    return tuple(out)


def structured_pair_bits(digit: int) -> tuple[int, int]:
    if digit == 0:  # -1
        return 0, 0
    if digit == 1:  # 0
        return 0, 1
    if digit == 2:  # +1
        return 1, 0
    raise ValueError(digit)


def pair_hamming(left: tuple[int, int], right: tuple[int, int]) -> int:
    return (left[0] != right[0]) + (left[1] != right[1])


def compact_local_antipode_stats() -> list[tuple[int, int, int]]:
    rows: list[tuple[int, int, int]] = []
    states = tuple(product(TRITS, repeat=9))
    for coordinate in range(9):
        total = 0
        maximum = 0
        for state in states:
            moved = flip_coordinate(state, coordinate)
            distance = hamming_int(rank3(state), rank3(moved))
            total += distance
            maximum = max(maximum, distance)
        rows.append((coordinate, total, maximum))
    return rows


def structured_local_antipode_stats() -> tuple[int, int]:
    total = 0
    maximum = 0
    for state in product(TRITS, repeat=9):
        before = structured_pair_bits(state[0])
        after = structured_pair_bits(antipode_digit(state[0]))
        distance = pair_hamming(before, after)
        total += distance
        maximum = max(maximum, distance)
    return total, maximum


def compact_rotation_stats() -> tuple[int, int]:
    total = 0
    maximum = 0
    for state in product(TRITS, repeat=9):
        distance = hamming_int(rank3(state), rank3(rotate90(state)))
        total += distance
        maximum = max(maximum, distance)
    return total, maximum


def main() -> None:
    compact = compact_local_antipode_stats()
    expected_compact = [
        (0, 26240, 14),
        (1, 39346, 14),
        (2, 49182, 13),
        (3, 63874, 13),
        (4, 69748, 14),
        (5, 79392, 14),
        (6, 100008, 14),
        (7, 102480, 14),
        (8, 99672, 13),
    ]
    assert compact == expected_compact, compact

    structured_total, structured_max = structured_local_antipode_stats()
    assert structured_total == 13122
    assert structured_max == 1

    rotation_total, rotation_max = compact_rotation_stats()
    assert rotation_total == 113000
    assert rotation_max == 12

    assert N == 19683
    assert 2**14 < N <= 2**15
    assert 2**15 - N == 13085

    print("T^9 states:", N)
    print("compact rank width: 15 bits; unused codewords:", 2**15 - N)
    print("structured per-trit width: 18 bits")
    print()
    print("compact 15-bit codec: local antipode")
    print("coordinate  total_hamming  max_hamming  mean_hamming")
    for coordinate, total, maximum in compact:
        print(f"{coordinate:>10}  {total:>13}  {maximum:>11}  {total / N:>12.9f}")
    print()
    print("structured 18-bit codec: one-coordinate antipode")
    print("total_hamming", structured_total)
    print("max_hamming", structured_max)
    print("mean_hamming", structured_total / N)
    print()
    print("compact 15-bit codec: 3x3 90-degree rotation")
    print("total_hamming", rotation_total)
    print("max_hamming", rotation_max)
    print("mean_hamming", rotation_total / N)
    print()
    print("BOUNDARY: these are exact results for the declared codecs, not a universal")
    print("lower bound over all binary encodings and not a hardware timing theorem.")


if __name__ == "__main__":
    main()
