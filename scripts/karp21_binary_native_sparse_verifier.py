#!/usr/bin/env python3
"""Binary-native deterministic sparse N21 weighted MAX CUT verifier.

Consumes the *original* gamma/zigzag signed graph-word format and
the *original* 2m-bit sparse certificate. It never instantiates
Fin n or a full n-entry label vector. Endpoints remain Python binary
integers; the consistency check is a deterministic pairwise scan,
with no reliance on average-case dictionary hashing.

This is a concrete Python executable reference, not an Agda kernel
theorem or formal Turing-machine cost receipt. Its direct semantics
are intended to match verifies_sparse_word() in the existing codec.
Attribution: Richard Karp (1972), DASHI original N21 binary codec
and 2m endpoint-certificate theorem owners.
"""
from __future__ import annotations

from typing import Sequence

from karp21_signed_cut_binary_codec import (
    Bits, _validate_bits, read_gamma_nat, unzigzag,
)


def verifies_sparse_word_binary_native(
    graph_word: Sequence[int],
    certificate: Sequence[int],
) -> bool:
    """Total fail-closed N21 language verifier, independent of n storage.

    The actual word format is read *once*, in original field order.
    For every edge, O(m) previously seen endpoint assignments are
    checked for contradictory use of the same original vertex ID.
    Signed weights are summed with arbitrary-precision exact integers.
    """
    try:
        word = _validate_bits(graph_word)
        bits = _validate_bits(certificate)
        n, offset = read_gamma_nat(word, 0)
        m, offset = read_gamma_nat(word, offset)

        if m > n * (n - 1) // 2:
            return False
        if 3 * m + 1 > len(word) - offset:
            return False
        if len(bits) != 2 * m:
            return False

        prev = (-1, -1)
        seen: list[tuple[int, int]] = []
        score = 0
        for j in range(m):
            u, offset = read_gamma_nat(word, offset)
            v, offset = read_gamma_nat(word, offset)
            signed_code, offset = read_gamma_nat(word, offset)
            w = unzigzag(signed_code)
            if not 0 <= u < v < n:
                return False
            if (u, v) <= prev:
                return False
            prev = (u, v)

            a, b = bits[2 * j], bits[2 * j + 1]
            for earlier_vertex, earlier_label in seen:
                if (earlier_vertex == u and earlier_label != a) or (
                    earlier_vertex == v and earlier_label != b
                ):
                    return False
            seen.append((u, a))
            seen.append((v, b))
            if a != b:
                score += w

        threshold, offset = read_gamma_nat(word, offset)
        if offset != len(word) or threshold <= 0:
            return False
        return score >= threshold
    except (ValueError, TypeError):
        return False


def pairwise_endpoint_comparison_count(m: int) -> int:
    """Exact number of previous-endpoint comparisons for m edges.

    At edge j there are 2j previous endpoint assignments. Each is
    inspected at most once, so total <= sum_{j<m} 2j = m(m-1).
    This counts logical comparisons, not their bit-tape cost.
    """
    if type(m) is not int or m < 0:
        raise ValueError("invalid edge count")
    return m * (m - 1)


def maximum_edges_from_canonical_input_bits(input_length: int) -> int:
    """Universal bound for this exact gamma graph grammar.

    There are at least two header bits (n,m), at least three gamma
    fields per edge, and at least one positive-threshold gamma bit.
    Hence for every accepted word 3*m + 3 <= input_length.
    This bound is independent of the potentially exponential n.
    """
    if type(input_length) is not int or input_length < 0:
        raise ValueError("negative graph word bit count")
    return max(0, (input_length - 3) // 3)


def binary_native_pairwise_comparisons_bound(input_length: int) -> int:
    """Deterministic worst-case count, not a Python machine-time bound."""
    m_max = maximum_edges_from_canonical_input_bits(input_length)
    return pairwise_endpoint_comparison_count(m_max)


if __name__ == "__main__":
    import sys
    print(
        "Binary-native N21 sparse verifier. "
        "Run scripts/check_karp21_binary_native_sparse_verifier.py "
        "for same-word regression."
    )
    sys.exit(0)
