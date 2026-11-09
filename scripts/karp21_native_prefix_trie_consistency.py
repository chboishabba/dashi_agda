"""Binary-address prefix trie for original N21 sparse endpoint occurrences.

Key = original native gamma successor bits (MSB-first), without constructing Nat.
A trie node contains an optional Boolean assignment, and two outgoing edges.
Only label conflicts cause rejection. Insertion performs one transition for
each key bit, unlike the previous all-history pairwise address comparison.

The implementation is a standalone primitive, not an Agda machine-clock proof.
"""
from dataclasses import dataclass, field
from typing import Optional, Sequence

@dataclass
class TrieNode:
    label: Optional[int] = None
    children: dict[int, 'TrieNode'] = field(default_factory=dict)

@dataclass
class TrieCost:
    bit_transitions: int = 0
    nodes_allocated: int = 1
    comparisons: int = 0

class EndpointTrie:
    def __init__(self):
        self.root = TrieNode()
        self.cost = TrieCost()

    def admit(self, key: Sequence[int], label: int) -> bool:
        if label not in (0, 1) or not key or key[0] != 1:
            return False
        node = self.root
        for bit in key:
            if bit not in (0, 1):
                return False
            self.cost.bit_transitions += 1
            self.cost.comparisons += 1
            if bit not in node.children:
                node.children[bit] = TrieNode()
                self.cost.nodes_allocated += 1
            node = node.children[bit]
        self.cost.comparisons += 1
        if node.label is None:
            node.label = label
            return True
        return node.label == label


def prefix_trie_consistent(occurrences):
    trie = EndpointTrie()
    for key, label in occurrences:
        if not trie.admit(key, label):
            return False, trie.cost
    return True, trie.cost


def verify_original_native_word_via_trie(graph_word, certificate):
    """Original native gamma graph parser, same 2m certificate, trie endpoint guard.

    This adapter reuses the already-authoritative Python parser and arithmetic.
    No alternative graph grammar or numerical bigint decoding is introduced.
    """
    from karp21_native_bitword_sparse_verifier import (
        InvalidWord, add_unsigned, compare_unsigned, parse_graph, strict_bits,
    )
    try:
        graph = parse_graph(graph_word)
        bits = strict_bits(certificate)
        if len(bits) != 2 * len(graph.edges):
            return False
        history = EndpointTrie()
        positive_sum, negative_sum = (), ()
        for i, (u, v, positive, weight) in enumerate(graph.edges):
            a, b = bits[2 * i], bits[2 * i + 1]
            if not history.admit(u, a) or not history.admit(v, b):
                return False
            if a != b:
                if positive:
                    positive_sum = add_unsigned(positive_sum, weight)
                else:
                    negative_sum = add_unsigned(negative_sum, weight)
        return compare_unsigned(
            positive_sum, add_unsigned(negative_sum, graph.threshold)
        ) >= 0
    except (InvalidWord, ValueError, TypeError):
        return False
