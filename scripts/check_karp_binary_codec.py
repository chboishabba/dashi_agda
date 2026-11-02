#!/usr/bin/env python3
"""Exhaustive small-instance checks for the concrete signed E20/N21 bit codec.

Checks *actual* binary source/target words rather than just graph algebra.
The source Agda owners still need a formal decoder/encoder correspondence
and a Turing machine cost theorem. This is a finite executable regression.
"""
from itertools import product

from karp21_signed_cut_binary_codec import (
    CutGraph, decode_graph, decode_partition, encode_graph, encode_partition,
    gamma_nat, read_gamma_nat, reduction_word, cut_score, verifies_word,
    partition_to_cut, signed_bits, sparse_certificate_from_labels,
    sparse_cut_certificate_verifier, verifies_sparse_word,
)


def test_gamma() -> int:
    for n in list(range(128)) + [2**k for k in (10, 63, 128, 1024)]:
        w = gamma_nat(n)
        recovered, end = read_gamma_nat(w, 0)
        assert recovered == n and end == len(w)
    for value in (-2**1024, -2**63, -1, 0, 1, 2**63, 2**1024):
        assert decode_partition(encode_partition((value,))) == (value,)
    return 139


def test_invalid_source_maps_to_no() -> None:
    no_graph = CutGraph(2, ((0, 1, 1),), 2)
    for word in ((), (0,), (1, 1), (0, 1), (0, 0), (2,), (-1,), (1, 0)):
        target = decode_graph(reduction_word(word))
        assert target == no_graph
        assert not any(
            verifies_word(encode_graph(target), labels)
            for labels in product((0, 1), repeat=target.vertices)
        )
    assert decode_graph(reduction_word(encode_partition((1, 2, 3)) + (0,))) == no_graph


def test_graph_parser_fail_closed() -> None:
    graph = CutGraph(4, ((0, 1, 2), (0, 3, -2), (2, 3, 5)), 2)
    canonical = encode_graph(graph)
    assert decode_graph(canonical) == graph
    for malformed in (
        canonical + (1,), canonical + (0,), canonical[:-1],
        # loop, reversed endpoints, two identical pairs, nonpositive W
        gamma_nat(2) + gamma_nat(1) +
            gamma_nat(0) + gamma_nat(0) + signed_bits(1) + gamma_nat(1),
        gamma_nat(2) + gamma_nat(1) +
            gamma_nat(1) + gamma_nat(0) + signed_bits(1) + gamma_nat(1),
        gamma_nat(2) + gamma_nat(2) +
            2*(gamma_nat(0)+gamma_nat(1)+signed_bits(1)) + gamma_nat(1),
        gamma_nat(2) + gamma_nat(1) +
            gamma_nat(0) + gamma_nat(1) + signed_bits(1) + gamma_nat(0),
        gamma_nat(2) + gamma_nat(2) + gamma_nat(1),
    ):
        assert not verifies_word(malformed, (0, 1, 0, 1))
    assert not verifies_word(canonical, (0, 1))
    assert not verifies_word(canonical, (0, 1, 1, 0, 0))
    assert not verifies_word(canonical, (0, 1, 2, 0))


def test_full_reduction() -> tuple[int, int]:
    cases = 0
    labels = 0
    for n in range(6):
        for parts in product((-2, -1, 0, 1, 2), repeat=n):
            source_bits = encode_partition(parts)
            assert decode_partition(source_bits) == parts
            cut = partition_to_cut(parts)
            target_bits = reduction_word(source_bits)
            parsed = decode_graph(target_bits)
            assert parsed == cut
            assert encode_graph(parsed) == target_bits
            assert len(target_bits) <= 128*(len(source_bits)+1)**3
            has_partition = False
            target_accepts = False
            for bits in product((0, 1), repeat=n):
                chosen = sum(x for x,b in zip(parts,bits) if b)
                balance = 2*chosen == sum(parts)
                has_partition |= balance
                # The exceptional zero-total case maps to a different,
                # fixed-sized 2-vertex graph. It is universally YES.
                if sum(parts) != 0:
                    assert verifies_word(target_bits,bits) == balance
                    assert cut_score(parsed,bits) == (
                        sum(parts)**2 - (2*chosen-sum(parts))**2
                    )
                    target_accepts |= verifies_word(target_bits,bits)
                labels += 1
            if sum(parts) == 0:
                assert verifies_word(target_bits,(1,0))
                target_accepts = True
            assert has_partition == target_accepts, (n,parts)
            cases += 1
    return cases,labels


def test_large_binary_weights() -> int:
    count = 0
    for n in range(9):
        for width in (0, 1, 2, 8, 64, 1024):
            parts = tuple((1 << width) if k % 2 == 0 else -(1 << width)
                          for k in range(n))
            source = encode_partition(parts)
            target = reduction_word(source)
            graph = decode_graph(target)
            assert graph == partition_to_cut(parts)
            assert len(target) <= 128 * (len(source)+1)**3
            count += 1
    return count




def test_sparse_endpoint_certificates() -> int:
    """N21 witness bit bound is 2m, not binary-encoded vertex count n.

    Huge n with only m=1 proves a genuine size counterexample to the
    earlier assertion that n bits is polynomial in graph Word length.
    """
    checks = 0
    for n in range(6):
        for parts in product((-2, -1, 0, 1, 2), repeat=n):
            graph = partition_to_cut(parts)
            encoded = encode_graph(graph)
            for labels in product((0, 1), repeat=graph.vertices):
                short = sparse_certificate_from_labels(graph, labels)
                assert len(short) == 2*len(graph.edges)
                assert verifies_sparse_word(encoded, short) == verifies_word(encoded, labels)
                checks += 1

    # A graph whose number of isolated vertices is exponential in its
    # binary graph word length has a 2-bit, rather than n-bit, witness.
    huge_n = 2**1024
    huge = CutGraph(huge_n, ((0, huge_n - 1, 3),), 1)
    huge_word = encode_graph(huge)
    assert len(huge_word) < 5000
    assert verifies_sparse_word(huge_word, (0, 1))
    assert not verifies_sparse_word(huge_word, (1, 1))
    assert not verifies_sparse_word(huge_word, (0,))
    assert not verifies_sparse_word(huge_word, (0, 1, 0))
    checks += 4

    repeated = CutGraph(3, ((0, 1, 3), (0, 2, 4)), 5)
    repeated_word = encode_graph(repeated)
    assert verifies_sparse_word(repeated_word, (0, 1, 0, 1))
    assert not verifies_sparse_word(repeated_word, (0, 1, 1, 1))
    # Even if individually crossing edges would pass, a vertex cannot
    # receive contradictory labels in two edge-local assignments.
    assert not verifies_sparse_word(repeated_word, (0, 1, 1, 0))
    checks += 3

    signed = CutGraph(3, ((0, 1, -5), (1, 2, 8)), 3)
    for labels in product((0, 1), repeat=3):
        assert verifies_sparse_word(
            encode_graph(signed), sparse_certificate_from_labels(signed, labels)
        ) == verifies_word(encode_graph(signed), labels)
        checks += 1
    return checks

if __name__ == "__main__":
    gamma = test_gamma()
    test_invalid_source_maps_to_no()
    test_graph_parser_fail_closed()
    n, witness_checks = test_full_reduction()
    large = test_large_binary_weights()
    sparse = test_sparse_endpoint_certificates()
    print(f"PASS exact E20 binary source/target codec: {n} source instances, "
          f"{witness_checks} bit-label checks; {large} 1024-bit envelope "
          f"controls; {gamma} gamma/signed int controls; malformed graph "
          f"and source words fail closed")
