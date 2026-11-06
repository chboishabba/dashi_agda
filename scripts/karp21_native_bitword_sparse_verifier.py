#!/usr/bin/env python3
"""Bit-native executable N21 signed MAX CUT verifier for the ORIGINAL wire grammar.

All graph vertex and edge endpoint addresses remain MSB-first binary
representations of gamma's n+1, never Peano Fin n or Vec Bool n. Signed
weights are parsed as binary sign/magnitude without zigzag Nat evaluation.
Original graph grammar:
  gamma(n) gamma(m) m * (gamma(u) gamma(v) gamma(zigzag(w))) gamma(W)
  ordered u<v<n, strict lexicographic edges, W>0 and no trailing bits.
Sparse certificate: exactly two bits per edge, repeated endpoints agree.

Proof authority: NONE. This is an executable reference/Agda implementation
target; equivalence with source-owned original GraphWord/fin-free Boolean
verifier must be proved in Agda before promotion.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Sequence

Bits = tuple[int, ...]

class InvalidWord(ValueError):
    pass

@dataclass(frozen=True)
class NativeGraph:
    vertex_successor: Bits
    edges: tuple[tuple[Bits, Bits, bool, Bits], ...]
    threshold: Bits

def strict_bits(word: Sequence[int]) -> Bits:
    if not isinstance(word, (tuple, list)):
        raise InvalidWord("expected a list/tuple of bits")
    if any(type(x) is not int or x not in (0, 1) for x in word):
        raise InvalidWord("not a Boolean word")
    return tuple(word)

def normalized(bits: Bits) -> Bits:
    i = 0
    while i < len(bits) and not bits[i]:
        i += 1
    return bits[i:]

def compare_unsigned(a: Bits, b: Bits) -> int:
    """Compare MSB-first canonical unsigned binary magnitudes."""
    a, b = normalized(a), normalized(b)
    if len(a) != len(b):
        return -1 if len(a) < len(b) else 1
    if a == b:
        return 0
    return -1 if a < b else 1

def add_unsigned(a: Bits, b: Bits) -> Bits:
    """Linear carry-propagation addition, with NO Python big-int arithmetic."""
    carry, result = 0, []
    ai, bi = len(a) - 1, len(b) - 1
    while ai >= 0 or bi >= 0 or carry:
        x = a[ai] if ai >= 0 else 0
        y = b[bi] if bi >= 0 else 0
        total = x + y + carry
        result.append(total & 1)
        carry = 1 if total >= 2 else 0
        ai -= 1
        bi -= 1
    return normalized(tuple(reversed(result)))

def successor_to_nat_bits(successor: Bits) -> Bits:
    """Binary decrement by one. Input gamma payload always begins with 1."""
    if not successor or successor[0] != 1:
        raise InvalidWord("invalid successor bits")
    result = list(successor)
    i = len(result) - 1
    while i >= 0 and result[i] == 0:
        result[i] = 1
        i -= 1
    if i < 0:
        raise InvalidWord("zero successor")
    result[i] = 0
    return normalized(tuple(result))

def read_gamma_successor(bits: Bits, offset: int) -> tuple[Bits, int]:
    """Strict gamma token, returns binary n+1 and next offset."""
    zeros, i = 0, offset
    while i < len(bits) and bits[i] == 0:
        zeros += 1
        i += 1
    if i == len(bits):
        raise InvalidWord("unterminated gamma header")
    end = i + zeros + 1
    if end > len(bits):
        raise InvalidWord("truncated gamma payload")
    return bits[i:end], end

def bounded_count(successor: Bits, cap: int) -> int:
    """Convert gamma(n) to a host loop count only after proven n<=cap.

    Never constructs a giant integer: stop at cap+1 while reading bits.
    """
    value = 0
    for bit in successor:
        value = 2 * value + bit
        if value > cap + 1:
            raise InvalidWord("declared list count exceeds input budget")
    n = value - 1
    if n > cap:
        raise InvalidWord("count exceeds input budget")
    return n

def read_signed_bits(bits: Bits, offset: int) -> tuple[bool, Bits, int]:
    """Last successor bit: 1 nonnegative, 0 negative."""
    successor, end = read_gamma_successor(bits, offset)
    return bool(successor[-1]), normalized(successor[:-1]), end

def parse_graph(word: Sequence[int]) -> NativeGraph:
    bits = strict_bits(word)
    vertex_successor, pos = read_gamma_successor(bits, 0)
    edge_count_successor, pos = read_gamma_successor(bits, pos)
    # An edge uses three nonempty gamma tokens. The threshold is extra.
    m = bounded_count(edge_count_successor, max(0, (len(bits) - pos) // 3))
    previous: tuple[Bits, Bits] | None = None
    edges: list[tuple[Bits, Bits, bool, Bits]] = []
    for _ in range(m):
        u, pos = read_gamma_successor(bits, pos)
        v, pos = read_gamma_successor(bits, pos)
        positive, magnitude, pos = read_signed_bits(bits, pos)
        if compare_unsigned(u, v) >= 0 or compare_unsigned(v, vertex_successor) >= 0:
            raise InvalidWord("out-of-range or noncanonical endpoint pair")
        if previous is not None:
            pu, pv = previous
            if compare_unsigned(pu, u) > 0 or (
                compare_unsigned(pu, u) == 0 and compare_unsigned(pv, v) >= 0
            ):
                raise InvalidWord("unordered or repeated edge")
        edges.append((u, v, positive, magnitude))
        previous = (u, v)
    threshold_successor, pos = read_gamma_successor(bits, pos)
    if pos != len(bits):
        raise InvalidWord("trailing graph bits")
    threshold = successor_to_nat_bits(threshold_successor)
    if not threshold:
        raise InvalidWord("MAX CUT threshold must be positive")
    return NativeGraph(vertex_successor, tuple(edges), threshold)

def verify_native_sparse_graph(graph: NativeGraph, certificate: Sequence[int]) -> bool:
    bits = strict_bits(certificate)
    if len(bits) != 2 * len(graph.edges):
        return False
    history: list[tuple[Bits, int]] = []
    positive_sum, negative_sum = (), ()
    for index, (u, v, positive, weight) in enumerate(graph.edges):
        a, b = bits[2 * index], bits[2 * index + 1]
        for old_addr, old_label in history:
            if (compare_unsigned(u, old_addr) == 0 and a != old_label) or (
                compare_unsigned(v, old_addr) == 0 and b != old_label
            ):
                return False
        history.append((u, a))
        history.append((v, b))
        if a != b:
            if positive:
                positive_sum = add_unsigned(positive_sum, weight)
            else:
                negative_sum = add_unsigned(negative_sum, weight)
    # signed score positive_sum - negative_sum >= W iff
    # positive_sum >= negative_sum + W.
    return compare_unsigned(
        positive_sum, add_unsigned(negative_sum, graph.threshold)
    ) >= 0

def verify_native_sparse_word(
    graph_word: Sequence[int], certificate: Sequence[int]
) -> bool:
    try:
        graph = parse_graph(graph_word)
        return verify_native_sparse_graph(graph, certificate)
    except (InvalidWord, ValueError, TypeError):
        return False

__all__ = [
    "InvalidWord", "NativeGraph", "add_unsigned", "compare_unsigned",
    "parse_graph", "read_gamma_successor", "read_signed_bits",
    "verify_native_sparse_word", "verify_native_sparse_graph",
]
