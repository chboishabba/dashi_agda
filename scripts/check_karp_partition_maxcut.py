#!/usr/bin/env python3
"""Finite arithmetic regression for Karp (1972) PARTITION -> weighted MAX CUT.

Source: R. M. Karp, "Reducibility Among Combinatorial Problems",
1972, DOI 10.1007/978-1-4684-2001-2_9, original p. 100.

DASHI reconstructs the exact scalar identity using arbitrary-precision
integers. These exhaustive bounded tests are independent computational
checks, NOT an Agda proof, bit-costed reduction, or kernel certificate.
Karp's threshold is a positive integer; this regression uses nonempty
strictly positive input parts, so T > 0 and threshold >= 1.
"""

from itertools import product


def threshold(parts: tuple[int, ...]) -> int:
    assert parts and all(x > 0 for x in parts)
    total = sum(parts)
    return (total * total + 3) // 4  # ceil(T^2/4)


def has_partition(parts: tuple[int, ...]) -> bool:
    total = sum(parts)
    return any(2 * sum(x for x, b in zip(parts, bits) if b) == total
               for bits in product((0, 1), repeat=len(parts)))


def cut_weight(parts: tuple[int, ...], bits: tuple[int, ...]) -> int:
    return sum(parts[i] * parts[j]
               for i in range(len(parts))
               for j in range(i + 1, len(parts))
               if bits[i] != bits[j])


def verify_instance(parts: tuple[int, ...]) -> None:
    total = sum(parts)
    target = threshold(parts)
    weights = []
    for bits in product((0, 1), repeat=len(parts)):
        a = sum(x for x, side in zip(parts, bits) if side)
        objective = cut_weight(parts, bits)
        assert objective == a * (total - a)
        assert 4 * objective == total * total - (total - 2 * a) ** 2
        assert objective == cut_weight(parts, tuple(1 - b for b in bits))
        weights.append(objective)
    assert (max(weights) >= target) == has_partition(parts)


def main() -> None:
    tested = 0
    for n in range(1, 7):
        for parts in product(range(1, 6), repeat=n):
            verify_instance(parts)
            tested += 1
    print(f"PASS: {tested} positive partition instances; full cut enumeration,"
          " exact identity, complemented cut, threshold equivalence")


if __name__ == "__main__":
    main()
