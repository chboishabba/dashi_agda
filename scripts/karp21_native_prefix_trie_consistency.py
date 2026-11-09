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
