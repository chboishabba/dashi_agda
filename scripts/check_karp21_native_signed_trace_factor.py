#!/usr/bin/env python3
"""Original-wire N21 trace-factor differential and operation-count regression.

Requires the original in-repo Python codec and native binary verifier.
Tests all sparse certificates for small signed graphs and many repeated
large signed weights. Numeric reference uses Python ints ONLY in tests.
"""
from itertools import combinations, product
from karp21_signed_cut_binary_codec import CutGraph, encode_graph
from karp21_native_bitword_sparse_verifier import (
    parse_graph, verify_native_sparse_word,
)
from karp21_native_signed_trace_factor import (
    replay_signed_trace, verifies_original_word_factorized,
)


def numeric(bits):
    return sum(b << i for i, b in enumerate(reversed(tuple(bits))))


def check_signed_replay():
    cases = 0
    for size in range(7):
        for values in product((-5, -2, -1, 0, 2, 5), repeat=size):
            trace = [(x >= 0, tuple(map(int, bin(abs(x))[2:]))) if x else
                     (True, ()) for x in values]
            pa, na, plain = replay_signed_trace(trace, grouped=False)
            pb, nb, grouped = replay_signed_trace(trace, grouped=True)
            assert (pa, na) == (pb, nb)
            assert numeric(pb) - numeric(nb) == sum(values)
            flipped = [(not sign, weight) for sign, weight in trace]
            fp, fn, _ = replay_signed_trace(flipped, grouped=True)
            assert (fp, fn) == (nb, pb)
            assert grouped.group_entries <= len(values)
            cases += 1
    return cases


def check_original_words():
    cases = 0
    for n in range(2, 5):
        edges = list(combinations(range(n), 2))
        for m in range(min(3, len(edges)) + 1):
            for positions in combinations(edges, m):
                for weights in product((-7, -1, 0, 1, 7), repeat=m):
                    for threshold in (1, 2, 9):
                        graph = CutGraph(n, tuple((u, v, w)
                            for (u, v), w in zip(positions, weights)), threshold)
                        word = encode_graph(graph)
                        assert parse_graph(word)
                        for certificate in product((0, 1), repeat=2 * m):
                            assert verifies_original_word_factorized(
                                word, certificate
                            ) == verify_native_sparse_word(word, certificate), (
                                graph, certificate
                            )
                            cases += 1
    huge = 1 << 1024
    graph = CutGraph(huge, ((0, huge - 1, -(1 << 500)),), 1)
    word = encode_graph(graph)
    for cert in ((), (0,), (0, 1), (1, 0), (1, 1), (0, 0)):
        assert verifies_original_word_factorized(
            word, cert) == verify_native_sparse_word(word, cert)
        cases += 1
    for word in ((), (0,), (1,), (1, 1), (0, 1), word + (0,)):
        for cert in ((), (0, 1), (0, 0, 1)):
            assert verifies_original_word_factorized(
                word, cert) == verify_native_sparse_word(word, cert)
            cases += 1
    return cases


def check_operation_reuse():
    huge_weight = tuple(map(int, bin((1 << 1024) + 13)[2:]))
    trace = [(True, huge_weight)] * 256
    plain_pos, plain_neg, plain_cost = replay_signed_trace(trace, grouped=False)
    grouped_pos, grouped_neg, grouped_cost = replay_signed_trace(trace, grouped=True)
    assert (plain_pos, plain_neg) == (grouped_pos, grouped_neg)
    assert grouped_cost.group_entries == 1
    print(
        "Repeated 1025-bit weight x256:",
        "plain add stages", plain_cost.add_stages,
        "factor add stages", grouped_cost.add_stages,
        "dictionary key bits", grouped_cost.dictionary_key_bits,
    )
    # This check does not claim a complete speedup: key hashing,
    # allocations, comparisons and tape simulation are still unpriced.
    return plain_cost.add_stages, grouped_cost.add_stages


if __name__ == "__main__":
    a = check_signed_replay()
    b = check_original_words()
    check_operation_reuse()
    print(f"PASS {a} signed trace replays and {b} original graph-word checks")
