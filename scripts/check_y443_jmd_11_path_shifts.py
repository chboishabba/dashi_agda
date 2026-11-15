#!/usr/bin/env python3
"""Independent Y443 original-source JMD path-shift certificates.

Exactly mirrors the 7x15 + 4x9 native Agda graph-rewriting receipts.
Checks every local operation against the literal Y443 adjacency graph,
then compares the terminal singleton with the claimed generator.
This is finite verification, not Agda group-semantics acceptance.
"""
from __future__ import annotations

NODES = ("a", "b1", "c1", "d1", "e1", "b2", "c2", "d2", "e2", "b3", "c3", "d3")
EDGES = {
    frozenset(pair) for pair in (
        ("a", "b1"), ("b1", "c1"), ("c1", "d1"), ("d1", "e1"),
        ("a", "b2"), ("b2", "c2"), ("c2", "d2"), ("d2", "e2"),
        ("a", "b3"), ("b3", "c3"), ("c3", "d3"),
    )
}
FIRST = ("d3", "c3", "b3", "a", "b1", "c1", "d1", "e1")
THIRD = ("a", "b2", "c2", "d2", "e2")


def backward_ops(n: int, i: int) -> tuple[tuple[str, int], ...]:
    return tuple(
        [("commute", p) for p in range(n - 1, n - 1 - i, -1)]
        + [("braid", n - 2 - i)]
        + [("commute", p) for p in range(n - 3 - i, -1, -1)]
        + [("cancel", p) for p in range(n, 0, -1)]
    )


def forward_ops(n: int, i: int) -> tuple[tuple[str, int], ...]:
    return tuple(
        [("commute", p) for p in range(n - 1, i + 1, -1)]
        + [("braid", i)]
        + [("commute", p) for p in range(i - 1, -1, -1)]
        + [("cancel", p) for p in range(n, 0, -1)]
    )


def evaluate(word: tuple[str, ...], ops: tuple[tuple[str, int], ...]) -> tuple[str, ...]:
    current = list(word)
    for turn, (kind, pos) in enumerate(ops, start=1):
        assert pos >= 0, (turn, pos)
        if kind == "cancel":
            assert pos + 2 <= len(current)
            a, b = current[pos:pos + 2]
            assert a == b, (turn, current, kind, pos)
            current[pos:pos + 2] = []
        elif kind == "commute":
            assert pos + 2 <= len(current)
            a, b = current[pos:pos + 2]
            assert a != b and frozenset((a, b)) not in EDGES, (turn, current, kind, pos)
            current[pos:pos + 2] = [b, a]
        elif kind == "braid":
            assert pos + 3 <= len(current)
            a, b, c = current[pos:pos + 3]
            assert a == c and frozenset((a, b)) in EDGES, (turn, current, kind, pos)
            current[pos:pos + 3] = [b, a, b]
        else:
            raise AssertionError(f"unknown rewrite {kind}")
        assert set(current).issubset(NODES)
    return tuple(current)


def main() -> None:
    count, moves = 0, 0
    for i in range(7):
        word = FIRST[::-1] + (FIRST[i + 1],) + FIRST
        ops = backward_ops(8, i)
        assert len(ops) == 15
        assert evaluate(word, ops) == (FIRST[i],)
        count += 1
        moves += len(ops)
    for i in range(4):
        word = THIRD + (THIRD[i],) + THIRD[::-1]
        ops = forward_ops(5, i)
        assert len(ops) == 9
        assert evaluate(word, ops) == (THIRD[i + 1],)
        count += 1
        moves += len(ops)
    assert (count, moves) == (11, 141)
    print("PASS JMD: 11 original source-graph path-shift certificates (141 local Coxeter moves)")


if __name__ == "__main__":
    main()
