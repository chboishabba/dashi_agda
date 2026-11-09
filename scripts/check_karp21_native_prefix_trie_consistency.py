#!/usr/bin/env python3
"""Compare N21 binary address trie to original pairwise history semantics.

The finite tests run the actual trie primitive; the integration fixtures
also execute the existing original native graph-word parser and verifier.
They are not Agda/kernel or complete machine-clock certificates.
"""
from itertools import product
from karp21_native_prefix_trie_consistency import (
    prefix_trie_consistent, verify_original_native_word_via_trie,
)
from karp21_native_bitword_sparse_verifier import verify_native_sparse_word
from karp21_signed_cut_binary_codec import CutGraph, encode_graph


def original_pairwise(occurrences):
    return all((key_a != key_b or label_a == label_b)
               for i, (key_a, label_a) in enumerate(occurrences)
               for key_b, label_b in occurrences[:i])


def check_history():
    keys = [(1,), (1, 0), (1, 1), (1, 0, 0)]
    alphabet = [(key, v) for key in keys for v in (0, 1)]
    tests = 0
    for size in range(6):
        for occurrences in product(alphabet, repeat=size):
            got, cost = prefix_trie_consistent(occurrences)
            assert got == original_pairwise(occurrences), occurrences
            assert cost.bit_transitions <= sum(len(key) for key, _ in occurrences)
            assert cost.nodes_allocated <= 1 + cost.bit_transitions
            tests += 1
    assert tests == 37449
    huge = (1,) + (0,) * 1023 + (1,)
    occurrences = [(huge, 0), ((1, 1), 1), (huge, 0)]
    ok, cost = prefix_trie_consistent(occurrences)
    assert ok and cost.bit_transitions == 2 * len(huge) + 2
    assert not prefix_trie_consistent(occurrences + [(huge, 1)])[0]
    return tests


def check_original_graph_words():
    count = 0
    for n in range(2, 5):
        for weights in product((-4, 0, 3), repeat=2):
            edge_pairs = ((0, 1), (0, n - 1)) if n > 2 else ((0, 1),)
            graph = CutGraph(n, tuple((u, v, weights[i])
                          for i, (u, v) in enumerate(edge_pairs)), 1)
            word = encode_graph(graph)
            for cert in product((0, 1), repeat=2 * len(edge_pairs)):
                assert verify_original_native_word_via_trie(
                    word, cert
                ) == verify_native_sparse_word(word, cert)
                count += 1
    huge_n = 1 << 1024
    graph = CutGraph(huge_n, ((0, huge_n - 1, 3),), 1)
    word = encode_graph(graph)
    for cert in ((), (0,), (0, 1), (1, 0), (1, 1), (0, 0)):
        assert verify_original_native_word_via_trie(
            word, cert
        ) == verify_native_sparse_word(word, cert)
        count += 1
    for malformed in ((), (0,), (1,), (1, 1), (0, 1), word + (0,)):
        for cert in ((), (0,), (0, 1)):
            assert verify_original_native_word_via_trie(
                malformed, cert
            ) == verify_native_sparse_word(malformed, cert)
            count += 1
    return count


if __name__ == "__main__":
    histories = check_history()
    graphs = check_original_graph_words()
    print(f"PASS {histories} binary history cases; {graphs} original graph/certificate comparisons")
