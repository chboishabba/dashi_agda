#!/usr/bin/env python3
"""Exact E20 signed-PARTITION -> MAX CUT gamma output-length audit.

This checks the ACTUAL scripts/karp21_signed_cut_binary_codec.py
encoder, not a fresh graph representation. It proves a finite,
machine-checkable formula for the exact bit count of an E20 output,
and checks a conservative universal cubic envelope on sampled words.

Mathematical envelope (valid canonical source words of length L >= 1):
* n <= L: each signed element requires at least one gamma bit.
* |c_i| < 2**L. Therefore |T|=|sum c_i| <= n*2**L <= 2**(2*L).
* Every signed weight 4*c_i*c_j has gamma/zigzag length <= 4L+7.
* Endpoint gamma lengths each <= 2L+3.
* Number of upper-triangle edges m <= L**2.
* gamma(n), gamma(m), gamma(T**2) combined <= 14L+9.
So the output length is at most (8L+13)L**2 + 14L+9,
which is <= 16*(L+1)**3. Zero-sum and malformed sources yield
fixed 16-bit targets, also covered by this envelope (even L=0).

WARNING: output size is NOT execution time. A real polynomial
bit-tape clock for the Python and Agda program, as well as
kernel-accepted source correctness, remain open. This script is a
non-authoritative executable regression/audit, not an Agda proof.
Historical attribution: Karp (1972), Elias gamma, existing DASHI
E20/N21 signed codec and verifier owners.
"""
from __future__ import annotations

import argparse
from itertools import product

from karp21_signed_cut_binary_codec import (
    CutGraph,
    decode_graph,
    decode_partition,
    encode_graph,
    encode_partition,
    gamma_nat,
    partition_to_cut,
    reduction_word,
    zigzag,
)


def gamma_len(n: int) -> int:
    if type(n) is not int or n < 0:
        raise ValueError("gamma length requires a nonnegative natural")
    return 2 * (n + 1).bit_length() - 1


def exact_partition_wire_len(parts: tuple[int, ...]) -> int:
    return gamma_len(len(parts)) + sum(gamma_len(zigzag(c)) for c in parts)


def exact_graph_wire_len(graph: CutGraph) -> int:
    graph.validate()
    return (
        gamma_len(graph.vertices)
        + gamma_len(len(graph.edges))
        + sum(
            gamma_len(u) + gamma_len(v) + gamma_len(zigzag(w))
            for u, v, w in graph.edges
        )
        + gamma_len(graph.threshold)
    )


def exact_e20_graph_wire_len(parts: tuple[int, ...]) -> int:
    """Compute the actual E20 output length without serializing it."""
    total = sum(parts)
    if total == 0:
        # Exactly the zero-total, two-vertex unit-YES graph.
        return exact_graph_wire_len(CutGraph(2, ((0, 1, 1),), 1))
    n = len(parts)
    m = n * (n - 1) // 2
    length = gamma_len(n) + gamma_len(m) + gamma_len(total * total)
    for u in range(n):
        for v in range(u + 1, n):
            length += (
                gamma_len(u)
                + gamma_len(v)
                + gamma_len(zigzag(4 * parts[u] * parts[v]))
            )
    return length


def cubic_envelope(word_length: int) -> int:
    if word_length < 0:
        raise ValueError("negative input word length")
    return 16 * (word_length + 1) ** 3


def check_source(parts: tuple[int, ...]) -> None:
    word = encode_partition(parts)
    assert len(word) == exact_partition_wire_len(parts)
    actual = reduction_word(word)
    assert len(actual) == exact_e20_graph_wire_len(parts)
    assert len(actual) == exact_graph_wire_len(partition_to_cut(parts))
    assert len(actual) <= cubic_envelope(len(word))
    assert decode_graph(actual) == partition_to_cut(parts)


def check_malformed(word: tuple[int, ...]) -> None:
    # Only call on malformed bitwords; source is rejected.
    try:
        decode_partition(word)
    except (TypeError, ValueError):
        pass
    else:
        raise AssertionError("not a malformed source word")
    actual = reduction_word(word)
    no = CutGraph(2, ((0, 1, 1),), 2)
    assert decode_graph(actual) == no
    assert len(actual) == 16
    assert len(actual) <= cubic_envelope(len(word))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=4)
    parser.add_argument("--max-weight", type=int, default=2)
    args = parser.parse_args()
    checked = 0
    weights = range(-args.max_weight, args.max_weight + 1)
    for n in range(args.max_n + 1):
        for parts in product(weights, repeat=n):
            check_source(parts)
            checked += 1

    for word in ((), (0,), (0, 0), (0, 1), (1, 1), (1, 0)):
        check_malformed(word)

    extremes = (
        (2**1024, -2**1024, 7),
        (-2**2048, 2**1023, -1, 9),
        (2**4096,),
        (-2**4096, 2**4096),
    )
    for parts in extremes:
        check_source(parts)
        checked += 1

    print(
        f"PASS E20 exact wire bit lengths and 16*(L+1)^3 envelope: "
        f"{checked} canonical source words, 6 malformed source words; "
        "incl. 1024--4096-bit signed weights."
    )
    print("NOT CERTIFIED: Agda proof, real bit-tape polynomial machine clock, Karp network.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
