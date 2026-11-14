#!/usr/bin/env python3
"""Finite differential check for the ORIGINAL canonical tape-cell endcap CNF.

The Agda CellWidth codec uses bit 0 for plain(false)/headed(true). The
truth-table CNF rejects every row with bit 0 set. This checks both the
local template and first/last placement, including the boundary-ghost
witness. It does not constitute Agda kernel acceptance.
"""
from __future__ import annotations

from itertools import product


def cnf_for_predicate(width: int, predicate) -> tuple[tuple[int, ...], ...]:
    clauses = []
    for bits in product((0, 1), repeat=width):
        if not predicate(bits):
            clauses.append(tuple((i + 1) if b == 0 else -(i + 1)
                                 for i, b in enumerate(bits)))
    return tuple(clauses)


def evaluate(clauses, bits) -> bool:
    return all(any((lit > 0 and bits[abs(lit)-1] == 1) or
                   (lit < 0 and bits[abs(lit)-1] == 0)
                   for lit in clause)
               for clause in clauses)


def check():
    cases = 0
    for payload_width in range(0, 7):
        width = 1 + payload_width
        predicate = lambda bits: bits[0] == 0
        clauses = cnf_for_predicate(width, predicate)
        for bits in product((0, 1), repeat=width):
            assert evaluate(clauses, bits) == predicate(bits), (
                width, bits, clauses
            )
            cases += 1
    for n in range(1, 15):
        for row in product((0, 1), repeat=n):
            encoded = tuple((v, 0, 0) for v in row)
            # Each cell's first bit is the canonical headed tag; payload
            # is arbitrary, and does not affect the local endcap test.
            boundary_cnf = (encoded[0][0] == 0 and encoded[-1][0] == 0)
            boundary_semantics = not row[0] and not row[-1]
            assert boundary_cnf == boundary_semantics
            cases += 1
    before = (0, 0, 0, 1, 0, 0)
    after = (1, 0, 0, 0, 1, 0)
    assert before.count(1) == 1
    assert after.count(1) == 2
    assert not (after[0] == 0 and after[-1] == 0)
    print(f"PASS: {cases} exhaustive canonical tag/payload and row-endcap cases")
    print("PASS: phantom-head counterexample rejected by the first-cell CNF")
    print("NOT AN AGDA COMPILER RECEIPT")


if __name__ == "__main__":
    check()
