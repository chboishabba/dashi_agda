#!/usr/bin/env python3
"""Same-graph-word regression for N21's binary-native sparse verifier.

Compares against the EXISTING signed graph-word verifier on exhaustive
small PARTITION images, adversarial malformed words, duplicate vertex
assignments, signed weights, and a one-edge graph with 2**1024 vertices.

This is finite executable testing, NOT an Agda equality proof, generic
polynomial bit-machine clock, NP-completeness certificate or use of an
independent replacement graph language.
"""
from __future__ import annotations

from itertools import product

from karp21_signed_cut_binary_codec import (
    CutGraph,
    encode_graph,
    encode_partition,
    partition_to_cut,
    reduction_word,
    sparse_certificate_from_labels,
    verifies_sparse_word,
    gamma_nat,
    signed_bits,
)
from karp21_binary_native_sparse_verifier import (
    verifies_sparse_word_binary_native,
    pairwise_endpoint_comparison_count,
    maximum_edges_from_canonical_input_bits,
    binary_native_pairwise_comparisons_bound,
)


def same_word(w, cert) -> None:
    original = verifies_sparse_word(w, cert)
    native = verifies_sparse_word_binary_native(w, cert)
    assert native == original, (w, cert, native, original)


def exhaustive_small() -> int:
    count = 0
    for n in range(6):
        for parts in product((-2, -1, 0, 1, 2), repeat=n):
            g = partition_to_cut(parts)
            wire = reduction_word(encode_partition(parts))
            assert wire == encode_graph(g)
            assert len(g.edges) <= maximum_edges_from_canonical_input_bits(len(wire))
            assert pairwise_endpoint_comparison_count(len(g.edges)) <= binary_native_pairwise_comparisons_bound(len(wire))
            for labels in product((0, 1), repeat=g.vertices):
                cert = sparse_certificate_from_labels(g, labels)
                same_word(wire, cert)
                count += 1
                if len(cert) > 1:
                    # Invalid size cases fail closed.
                    same_word(wire, cert[:-1])
                    same_word(wire, cert + (0,))
                    count += 2
    return count


def small_malformed_words() -> int:
    count = 0
    for length in range(12):
        for word in product((0, 1), repeat=length):
            for cert in ((), (0,), (1,), (0, 1), (1, 0), (0, 1, 1, 0)):
                same_word(word, cert)
                count += 1
    return count


def huge_sparse_and_signed() -> int:
    count = 0
    huge_n = 2**1024
    sparse = CutGraph(huge_n, ((0, huge_n - 1, 3),), 1)
    assert len(sparse.edges) <= maximum_edges_from_canonical_input_bits(len(encode_graph(sparse)))
    for cert in ((), (0,), (0, 1), (1, 0), (1, 1), (0, 0)):
        same_word(encode_graph(sparse), cert)
        count += 1

    repeated = CutGraph(3, ((0, 1, 3), (0, 2, 4)), 5)
    for cert in product((0, 1), repeat=4):
        same_word(encode_graph(repeated), cert)
        count += 1

    signed = CutGraph(3, ((0, 1, -5), (1, 2, 8)), 3)
    for cert in product((0, 1), repeat=4):
        same_word(encode_graph(signed), cert)
        count += 1

    bad = [
        gamma_nat(2) + gamma_nat(2)
            + 2 * (gamma_nat(0) + gamma_nat(1) + signed_bits(1))
            + gamma_nat(1),
        gamma_nat(2) + gamma_nat(1)
            + gamma_nat(0) + gamma_nat(0)
            + signed_bits(1) + gamma_nat(1),
        gamma_nat(2) + gamma_nat(1)
            + gamma_nat(0) + gamma_nat(1)
            + signed_bits(1) + gamma_nat(0),
    ]
    for wire in bad:
        for cert in ((), (0, 1), (0, 1, 0, 1)):
            same_word(wire, cert)
            count += 1

    for m in range(100):
        assert pairwise_endpoint_comparison_count(m) == 2 * sum(range(m))
        count += 1
    return count


def main() -> int:
    a = exhaustive_small()
    b = small_malformed_words()
    c = huge_sparse_and_signed()
    print(
        f"PASS binary-native N21 same-word regression: "
        f"{a} signed PARTITION-label cases, {b} arbitrary short-word cases, "
        f"{c} huge-n/signed/repeated endpoint cases."
    )
    print(
        "NO KERNEL/MACHINE CLOCK CLAIM: source equality over all words "
        "and the formal bit-tape cost model remain to be proved in Agda."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
