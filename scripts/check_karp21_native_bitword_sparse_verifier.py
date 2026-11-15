#!/usr/bin/env python3
"""Differential check: bit-native original-word N21 verifier vs existing Python.

All generated inputs use the ORIGINAL gamma/zigzag graph grammar. Includes
negative weights, zero/positive weights, certificate conflicts, malformed words
and sparse graphs with enormous binary vertex counts. This is finite testing,
NOT an Agda proof or bit-TM clock certificate.
"""
from itertools import combinations, product
from karp21_signed_cut_binary_codec import (
    CutGraph, encode_graph, verifies_sparse_word, gamma_nat,
    zigzag, decode_graph,
)
from karp21_native_bitword_sparse_verifier import (
    parse_graph, read_signed_bits, verify_native_sparse_word,
    add_unsigned, compare_unsigned,
)

def bit_nat(bits):
    return int("".join(map(str, bits)) or "0", 2)

def check_signed_tokens():
    count = 0
    for value in range(-200, 201):
        code = gamma_nat(zigzag(value))
        sign, magnitude, pos = read_signed_bits(code, 0)
        restored = bit_nat(magnitude) if sign else -bit_nat(magnitude)
        assert (restored, pos) == (value, len(code))
        count += 1
    return count

def check_graphs():
    count = 0
    for n in range(2, 6):
        possible = list(combinations(range(n), 2))
        for m in range(min(len(possible), 3) + 1):
            for edge_slots in list(combinations(possible, m))[:8 if m == 3 else None]:
                for signed_weights in product((-3, 0, 2), repeat=m):
                    for threshold in (1, 2, 4):
                        graph = CutGraph(
                            n,
                            tuple((u, v, w)
                                  for (u, v), w in zip(edge_slots, signed_weights)),
                            threshold,
                        )
                        word = encode_graph(graph)
                        native = parse_graph(word)
                        assert bit_nat(native.vertex_successor) - 1 == n
                        assert len(native.edges) == m
                        assert bit_nat(native.threshold) == threshold
                        for witness in product((0, 1), repeat=2*m):
                            got = verify_native_sparse_word(word, witness)
                            original = verifies_sparse_word(word, witness)
                            assert got == original, (graph, witness, got, original)
                            count += 1
                        for invalid in (word + (0,), word + (1,), word[:-1]):
                            assert verify_native_sparse_word(invalid, (0,)* (2*m)) == verifies_sparse_word(
                                invalid, (0,) * (2*m))
    return count

def check_sparse_large_vertex():
    n = 1 << 1024
    graph = CutGraph(n, ((0, 1, 1),), 1)
    word = encode_graph(graph)
    assert verify_native_sparse_word(word, (0, 1))
    assert verifies_sparse_word(word, (0, 1))
    assert not verify_native_sparse_word(word, (1, 1))
    assert not verify_native_sparse_word(word, (0,))
    return len(word)

def check_malformed():
    words = [(), (0,), (1,), (0, 1), (0, 0, 0), (1, 1),
             (1, 1, 1), (1, 1, 0), (0, 1, 0)]
    for bits in words:
        for cert in ((), (0,), (0, 1), (1, 1, 1)):
            assert verify_native_sparse_word(bits, cert) == verifies_sparse_word(bits, cert)

def check_binary_add():
    count = 0
    for a in range(128):
        for b in range(128):
            abits = tuple(map(int, bin(a)[2:])) if a else ()
            bbits = tuple(map(int, bin(b)[2:])) if b else ()
            result = add_unsigned(abits, bbits)
            assert bit_nat(result) == a + b
            assert compare_unsigned(abits, bbits) == ((a > b) - (a < b))
            count += 1
    return count

def main():
    adds = check_binary_add()
    signed = check_signed_tokens()
    graphs = check_graphs()
    large_bits = check_sparse_large_vertex()
    check_malformed()
    print(
        f"PASS native N21: {adds} binary add/compare, "
        f"{signed} signed gamma tokens, {graphs} original graph/witness pairs, "
        f"sparse n=2^1024 ({large_bits} encoded bits), malformed cases"
    )

if __name__ == "__main__":
    main()
