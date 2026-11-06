#!/usr/bin/env python3
"""Deterministic counterexample to unrestricted local-window-to-unique-head.

Original grammar: ConcreteTapeLocalWindowPatternsExact.agda; original scanner:
ConcreteTapeWholeRowLocalityExact.scanWindowsCells.

The counterexample is a valid right-moving central step PLUS a disjoint
phantom head at the first cell, licensed by right-overlap-plus-two at the
row boundary. It disproves any theorem claiming that 'one interior old
head + equal row width + all individual windows legal' implies exactly
one new head without a boundary/anchoring invariant.

This is a finite computational witness, not an Agda kernel receipt.
"""
from __future__ import annotations

from dataclasses import dataclass

@dataclass(frozen=True)
class Plain:
    symbol: str

@dataclass(frozen=True)
class Headed:
    state: str
    symbol: str


def right_move_window_grammar(old, new, source, target, read, write):
    # Match ALL literal source grammar cases relevant for a moveRight rule.
    p = Plain
    h = Headed
    a, b, c = old
    x, y, z = new
    if all(isinstance(t, Plain) for t in old) and old == new:
        return "legal-unchanged"
    if (
        isinstance(a, Plain) and b == h(source, read)
        and isinstance(c, Plain) and x == a
        and y == p(write) and z == h(target, c.symbol)
    ):
        return "legal-centered realizes-right"
    if (
        isinstance(a, Plain) and isinstance(b, Plain)
        and c == h(source, read) and x == a and y == b and z == p(write)
    ):
        return "right-overlap-minus-one"
    if (
        a == h(source, read) and isinstance(b, Plain)
        and isinstance(c, Plain) and x == p(write)
        and y == h(target, b.symbol) and z == c
    ):
        return "right-overlap-plus-one"
    if (
        all(isinstance(t, Plain) for t in old)
        and x == h(target, a.symbol) and y == b and z == c
    ):
        return "right-overlap-plus-two"
    return None


def check():
    p = Plain("x")
    old = [p] * 9
    old[5] = Headed("q", "x")
    new = [p] * 9
    new[0] = Headed("qprime", "x")
    new[6] = Headed("qprime", "x")
    expected = [
        "right-overlap-plus-two",
        "legal-unchanged", "legal-unchanged",
        "right-overlap-minus-one",
        "legal-centered realizes-right",
        "right-overlap-plus-one", "right-overlap-plus-two",
    ]
    got = [
        right_move_window_grammar(
            old[i:i+3], new[i:i+3], "q", "qprime", "x", "x"
        )
        for i in range(7)
    ]
    assert got == expected, (got, expected)
    assert len(old) == len(new) == 9
    assert [i for i, t in enumerate(old) if isinstance(t, Headed)] == [5]
    assert [i for i, t in enumerate(new) if isinstance(t, Headed)] == [0, 6]
    # The old head is interior, not at either tape boundary.
    assert isinstance(old[4], Plain) and isinstance(old[6], Plain)
    print("PASS: all 7 original directional windows are legal")
    print("PASS: unique interior old head at 5; phantom+real new heads at 0,6")
    print("REFUTED: original global legality implies ExactlyOneHead after")
    return 0


if __name__ == "__main__":
    raise SystemExit(check())
