#!/usr/bin/env python3
"""Bounded arithmetic regression: signed Karp PARTITION -> weighted MAX CUT.

Primary: Richard M. Karp (1972), "Reducibility Among Combinatorial
Problems", p. 100. DOI 10.1007/978-1-4684-2001-2_9.

The original PARTITION input lies in Z^s and MAX CUT weights are integers,
with a POSITIVE integer threshold. For T=sum(c_i) != 0, use the complete
graph weights w(i,j)=c_i*c_j and threshold ceil(T*T/4). When T=0, a
partition always exists (the empty side works); map that case to a fixed
positive-threshold YES graph (2 vertices, edge weight 1, threshold 1).

These finite exhaustive runs are independent computational controls, NOT
a bit-costed polynomial reduction proof or Agda/Lean kernel certificate.
"""

from itertools import product


def has_partition(parts: tuple[int, ...]) -> bool:
    total = sum(parts)
    return any(2 * sum(x for x, b in zip(parts, bits) if b) == total
               for bits in product((0, 1), repeat=len(parts)))


def cut_weight(parts: tuple[int, ...], bits: tuple[int, ...]) -> int:
    return sum(parts[i] * parts[j]
               for i in range(len(parts))
               for j in range(i + 1, len(parts))
               if bits[i] != bits[j])


def reduce_partition_to_cut(
    parts: tuple[int, ...]
) -> tuple[int, list[tuple[int, int, int]], int]:
    total = sum(parts)
    if total == 0:
        return 2, [(0, 1, 1)], 1
    edges = [(i, j, parts[i] * parts[j])
             for i in range(len(parts))
             for j in range(i + 1, len(parts))]
    return len(parts), edges, (total * total + 3) // 4


def max_cut(n: int, edges: list[tuple[int, int, int]]) -> int:
    return max(sum(w for i, j, w in edges if bits[i] != bits[j])
               for bits in product((0, 1), repeat=n))


def verify_instance(parts: tuple[int, ...]) -> None:
    total = sum(parts)
    for bits in product((0, 1), repeat=len(parts)):
        subtotal = sum(x for x, side in zip(parts, bits) if side)
        objective = cut_weight(parts, bits)
        assert objective == subtotal * (total - subtotal)
        assert 4 * objective == total * total - (total - 2 * subtotal) ** 2
        assert objective == cut_weight(parts, tuple(1 - b for b in bits))
    n, edges, threshold = reduce_partition_to_cut(parts)
    assert threshold > 0
    assert (max_cut(n, edges) >= threshold) == has_partition(parts)


def test_printed_1972_threshold_counterexample() -> None:
    """Karp p.100 prints [1/4 sum_i c_i^2]; the literal square placement
    does NOT yield the stated equivalence. This is a textual formula audit,
    not a claim of discovering a new NP-hardness theorem.
    """
    parts = (2, 1)
    original_printed_threshold = (sum(x*x for x in parts) + 3) // 4
    repaired_threshold = threshold_for_nonzero_total(parts)
    assert not has_partition(parts)
    assert original_printed_threshold == 2
    assert repaired_threshold == 3
    assert cut_weight(parts, (0, 1)) == 2
    assert cut_weight(parts, (0, 1)) >= original_printed_threshold
    assert cut_weight(parts, (0, 1)) < repaired_threshold


def threshold_for_nonzero_total(parts: tuple[int, ...]) -> int:
    total = sum(parts)
    assert total != 0
    return (total * total + 3) // 4


def main() -> None:
    positive_count = 0
    for n in range(1, 7):
        for parts in product(range(1, 6), repeat=n):
            verify_instance(parts)
            positive_count += 1

    signed_count = 0
    for n in range(0, 6):
        for parts in product(range(-2, 3), repeat=n):
            verify_instance(parts)
            signed_count += 1

    test_printed_1972_threshold_counterexample()
    print("PASS Karp p.100 printed-threshold counterexample (2, 1); "
          "repaired square-of-total formulation distinguished")
    print(f"PASS: {positive_count} positive and {signed_count} signed/zero "
          "partition instances; exact quadratic cut identity, both side "
          "orientations, zero-total mapping and threshold equivalence")


if __name__ == "__main__":
    main()
