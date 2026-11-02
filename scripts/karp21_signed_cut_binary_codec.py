#!/usr/bin/env python3
"""Concrete Karp E20 signed PARTITION -> MAX CUT binary-word transducer.

Source original: R. M. Karp (1972), PARTITION -> MAX CUT.
DASHI variant: edge weight 4*c[i]*c[j], W=(sum c)**2, fixed 2-vertex
unit-edge YES target for sum=0. The existing Agda owners prove the
*typed finite semantic* equivalence; this executable codec is a source
implementation for the separate, still-unpaid Agda binary Word/machine
cost correspondence. No NP-completeness kernel receipt is claimed.

Bits are Python integers 0/1; binary words are tuple[int, ...].
Prefix code: gamma(n+1) for each NAT n; signed values use zigzag:
 n=2*z if z>=0, n=-2*z-1 otherwise.
Graph word:
 gamma(n), gamma(m), ordered m triples [gamma(u),gamma(v),gamma(zigzag(w))]
 followed by gamma(W). Require 0<=u<v<n; strictly sorted pair order;
 1<=W; no trailing data. No loops, reversed or duplicate edges.
Source word:
 gamma(source_count), followed by gamma(zigzag(source_i)) per position.
Invalid encodings fail *closed* via ValueError; target invalid inputs
never count as accepted instances.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from typing import Sequence, TypeAlias

Bits: TypeAlias = tuple[int, ...]
Edge: TypeAlias = tuple[int, int, int]


def _validate_bits(word: Sequence[int]) -> Bits:
    if not isinstance(word, (tuple, list)):
        raise ValueError("bit word must be a list/tuple")
    if any(type(bit) is not int or bit not in (0, 1) for bit in word):
        raise ValueError("invalid nonbinary digit")
    return tuple(word)


def gamma_nat(number: int) -> Bits:
    if type(number) is not int or number < 0:
        raise ValueError("gamma_natural requires nonnegative integer")
    digits = tuple(int(b) for b in bin(number + 1)[2:])
    return (0,) * (len(digits) - 1) + digits


def read_gamma_nat(word: Bits, offset: int) -> tuple[int, int]:
    if offset < 0 or offset >= len(word):
        raise ValueError("truncated natural number")
    prefix = 0
    while offset + prefix < len(word) and word[offset + prefix] == 0:
        prefix += 1
    if offset + prefix >= len(word):
        raise ValueError("unterminated gamma prefix")
    end = offset + 2 * prefix + 1
    if end > len(word):
        raise ValueError("truncated gamma payload")
    value = 0
    for bit in word[offset + prefix:end]:
        value = 2 * value + bit
    return value - 1, end


def zigzag(signed: int) -> int:
    if type(signed) is not int:
        raise ValueError("signed source value required")
    return 2 * signed if signed >= 0 else -2 * signed - 1


def unzigzag(number: int) -> int:
    if number < 0:
        raise ValueError("negative encoded zigzag value")
    return number // 2 if number % 2 == 0 else -(number // 2) - 1


def signed_bits(value: int) -> Bits:
    return gamma_nat(zigzag(value))


def _read_signed(word: Bits, offset: int) -> tuple[int, int]:
    number, offset = read_gamma_nat(word, offset)
    return unzigzag(number), offset


def encode_partition(parts: Sequence[int]) -> Bits:
    if any(type(x) is not int for x in parts):
        raise ValueError("partition values must be signed integers")
    bits = gamma_nat(len(parts))
    for x in parts:
        bits += signed_bits(x)
    return bits


def decode_partition(input_word: Sequence[int]) -> tuple[int, ...]:
    bits = _validate_bits(input_word)
    n, pos = read_gamma_nat(bits, 0)
    # Lower bound one code bit per source element; reject bomb lengths.
    if n > len(bits) - pos:
        raise ValueError("declared partition length exceeds remaining bits")
    parts = []
    for _ in range(n):
        x, pos = _read_signed(bits, pos)
        parts.append(x)
    if pos != len(bits):
        raise ValueError("trailing source bits")
    return tuple(parts)


@dataclass(frozen=True)
class CutGraph:
    vertices: int
    edges: tuple[Edge, ...]
    threshold: int

    def validate(self) -> None:
        if type(self.vertices) is not int or self.vertices < 0:
            raise ValueError("invalid vertex count")
        if type(self.threshold) is not int or self.threshold <= 0:
            raise ValueError("Karp MAX CUT requires positive threshold")
        previous = (-1, -1)
        for u, v, w in self.edges:
            if any(type(x) is not int for x in (u, v, w)):
                raise ValueError("malformed edge tuple")
            if not 0 <= u < v < self.vertices:
                raise ValueError("edge loop, orientation or range invalid")
            if (u, v) <= previous:
                raise ValueError("duplicate or unordered edge")
            previous = (u, v)


def encode_graph(graph: CutGraph) -> Bits:
    graph.validate()
    payload = gamma_nat(graph.vertices) + gamma_nat(len(graph.edges))
    for u, v, w in graph.edges:
        payload += gamma_nat(u) + gamma_nat(v) + signed_bits(w)
    return payload + gamma_nat(graph.threshold)


def decode_graph(input_word: Sequence[int]) -> CutGraph:
    word = _validate_bits(input_word)
    n, offset = read_gamma_nat(word, 0)
    m, offset = read_gamma_nat(word, offset)
    if m > n * (n - 1) // 2:
        raise ValueError("too many simple graph edges")
    # Each triple consumes at least 3 bits, and W needs >=1 bit.
    if 3 * m + 1 > len(word) - offset:
        raise ValueError("truncated edge tuples")
    edges = []
    previous = (-1, -1)
    for _ in range(m):
        u, offset = read_gamma_nat(word, offset)
        v, offset = read_gamma_nat(word, offset)
        w, offset = _read_signed(word, offset)
        if not 0 <= u < v < n or (u, v) <= previous:
            raise ValueError("noncanonical, duplicate or malformed edge")
        edges.append((u, v, w))
        previous = (u, v)
    threshold, offset = read_gamma_nat(word, offset)
    if offset != len(word):
        raise ValueError("trailing graph bits")
    graph = CutGraph(n, tuple(edges), threshold)
    graph.validate()
    return graph


def partition_to_cut(parts: Sequence[int]) -> CutGraph:
    source = tuple(parts)
    if any(type(x) is not int for x in source):
        raise ValueError("partition source is not signed integers")
    total = sum(source)
    if total == 0:
        return CutGraph(2, ((0, 1, 1),), 1)
    graph = CutGraph(
        len(source),
        tuple((u, v, 4 * source[u] * source[v])
              for u, v in combinations(range(len(source)), 2)),
        total * total,
    )
    graph.validate()
    return graph


def reduction_word(source_word: Sequence[int]) -> Bits:
    # TOTAL map on the Boolean-word carrier (and fail-closed on invalid
    # host input). Malformed source strings are false in source language;
    # therefore map them to a *valid* two-vertex fixed-NO Max-Cut graph.
    # This is necessary for reductions quantified over EVERY input Word.
    try:
        parts = decode_partition(source_word)
    except (ValueError, TypeError):
        return encode_graph(CutGraph(2, ((0, 1, 1),), 2))
    return encode_graph(partition_to_cut(parts))


def cut_score(graph: CutGraph, labels: Sequence[int]) -> int:
    if len(labels) != graph.vertices or any(bit not in (0, 1) for bit in labels):
        raise ValueError("invalid cut certificate")
    return sum(w for u, v, w in graph.edges if labels[u] != labels[v])


def verifies_cut(graph: CutGraph, labels: Sequence[int]) -> bool:
    return cut_score(graph, labels) >= graph.threshold


def verifies_word(graph_word: Sequence[int], certificate: Sequence[int]) -> bool:
    # The NP verifier is total and fail-closed on both malformed payloads.
    try:
        graph = decode_graph(graph_word)
        word = _validate_bits(certificate)
        return verifies_cut(graph, word)
    except (ValueError, TypeError):
        return False
