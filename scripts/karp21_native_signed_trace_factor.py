#!/usr/bin/env python3
"""Original N21 signed-edge trace factorization by identical binary weights.

Original gamma-encoded graph/sparse certificate semantics are unchanged.
A trace consists of selected (sign, magnitude) edge contributions; identical
signed weights share one dictionary entry with a binary occurrence counter.
The replay computes count * magnitude using shift/add, not Python big-int
arithmetic or FRACTRAN prime-power expansion.

This is an SSP-style valuation/multiplicity experiment, *not* a claim to run
the actual Monster group or a provably faster universal Karp verifier.
"""
from dataclasses import dataclass
from typing import Sequence


def canon(bits):
    bits = tuple(bits)
    i = 0
    while i < len(bits) and bits[i] == 0:
        i += 1
    return bits[i:]


@dataclass
class BitCost:
    add_stages: int = 0
    address_bit_visits: int = 0
    dictionary_key_bits: int = 0
    group_entries: int = 0


def add_binary(a, b, cost):
    a, b = canon(a), canon(b)
    out, carry = [], 0
    for i in range(max(len(a), len(b))):
        x = a[-1 - i] if i < len(a) else 0
        y = b[-1 - i] if i < len(b) else 0
        s = x + y + carry
        out.append(s & 1)
        carry = s >> 1
        cost.add_stages += 1
    if carry:
        out.append(1)
        cost.add_stages += 1
    return canon(reversed(out))


def multiply_by_binary_count(weight, count_bits, cost):
    """Schoolbook binary shift/add, count supplied as an actual bitword."""
    acc, shifted = (), canon(weight)
    for bit in reversed(count_bits):
        if bit:
            acc = add_binary(acc, shifted, cost)
        shifted = shifted + (0,) if shifted else ()
    return acc


def increment_binary(count_bits, cost):
    return add_binary(count_bits, (1,), cost)


def replay_signed_trace(contributions, *, grouped):
    """(positive,total), (negative,total), cost, group count."""
    cost = BitCost()
    pos, neg = (), ()
    if grouped:
        classes = {}
        for sign, weight in contributions:
            key = (sign, canon(weight))
            cost.dictionary_key_bits += len(key[1]) + 1
            classes[key] = increment_binary(classes.get(key, ()), cost)
        cost.group_entries = len(classes)
        for (sign, weight), count in classes.items():
            contribution = multiply_by_binary_count(weight, count, cost)
            if sign:
                pos = add_binary(pos, contribution, cost)
            else:
                neg = add_binary(neg, contribution, cost)
    else:
        cost.group_entries = len(contributions)
        for sign, weight in contributions:
            if sign:
                pos = add_binary(pos, weight, cost)
            else:
                neg = add_binary(neg, weight, cost)
    return pos, neg, cost


def original_graph_trace(graph, certificate):
    """Use exactly the existing native Graph and 2m endpoint certificate."""
    from karp21_native_bitword_sparse_verifier import strict_bits
    bits = strict_bits(certificate)
    if len(bits) != 2 * len(graph.edges):
        raise ValueError("incorrect sparse certificate size")
    # The original repeated-vertex check is left untouched; this routine
    # is intentionally applied only AFTER the original verifier's guard.
    return [(positive, magnitude)
            for i, (_u, _v, positive, magnitude) in enumerate(graph.edges)
            if bits[2 * i] != bits[2 * i + 1]]


def verifies_original_word_factorized(graph_word, certificate):
    from karp21_native_bitword_sparse_verifier import (
        InvalidWord, compare_unsigned, parse_graph, strict_bits,
    )
    from karp21_native_prefix_trie_consistency import EndpointTrie
    try:
        graph = parse_graph(graph_word)
        bits = strict_bits(certificate)
        if len(bits) != 2 * len(graph.edges):
            return False
        trie = EndpointTrie()
        for i, (u, v, _positive, _weight) in enumerate(graph.edges):
            if not trie.admit(u, bits[2 * i]) or not trie.admit(v, bits[2 * i + 1]):
                return False
        trace = original_graph_trace(graph, bits)
        pos, neg, _cost = replay_signed_trace(trace, grouped=True)
        cost = BitCost()
        from karp21_native_bitword_sparse_verifier import add_unsigned
        return compare_unsigned(pos, add_unsigned(neg, graph.threshold)) >= 0
    except (InvalidWord, ValueError, TypeError):
        return False
