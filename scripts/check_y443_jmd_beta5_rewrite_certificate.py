#!/usr/bin/env python3
"""Source-exact Coxeter A4/JMD beta^5 certificate: 35 checked rewrites.

JMD beta = x5*x6*x7*x8 on the Y443 length-four arm.
The Coxeter presentation says each x_i is an involution, adjacent
x_i,x_{i+1} have product order 3, and nonadjacent commute.
An adjacent order-three relation with involutions is equivalent to
the braid law a b a = b a b. Thus the operations here are sound
CONSEQUENCES of the original Y443 presentation, not probabilistic
word equality in a permutation model.

This independently verifies the finite combinatorial derivation of
beta^5=1; native Agda group-semantics acceptance remains a separate gate.
"""

from __future__ import annotations

BETA = (5, 6, 7, 8)
OPS = (
    ("commute", 3), ("commute", 2), ("commute", 4),
    ("braid", 0), ("braid", 2), ("braid", 4), ("cancel", 6),
    ("commute", 1), ("commute", 3), ("commute", 2),
    ("commute", 5), ("braid", 3), ("braid", 5),
    ("cancel", 7), ("commute", 4), ("commute", 6),
    ("commute", 5), ("braid", 6), ("cancel", 8),
    ("commute", 7), ("commute", 8), ("cancel", 9),
    ("commute", 2), ("braid", 0), ("braid", 2),
    ("cancel", 4), ("commute", 1), ("braid", 2),
    ("cancel", 4), ("commute", 3), ("cancel", 4),
    ("braid", 0), ("cancel", 2), ("cancel", 1),
    ("cancel", 0),
)


def apply(word: tuple[int, ...], action: str, pos: int) -> tuple[int, ...]:
    assert pos >= 0
    if action == "cancel":
        assert pos + 2 <= len(word)
        a, b = word[pos:pos + 2]
        assert a == b
        out = word[:pos] + word[pos + 2:]
    elif action == "commute":
        assert pos + 2 <= len(word)
        a, b = word[pos:pos + 2]
        assert a != b and abs(a - b) >= 2
        out = word[:pos] + (b, a) + word[pos + 2:]
    elif action == "braid":
        assert pos + 3 <= len(word)
        a, b, c = word[pos:pos + 3]
        assert a == c and abs(a - b) == 1
        out = word[:pos] + (b, a, b) + word[pos + 3:]
    else:
        raise ValueError(f"unknown local Coxeter rule: {action}")
    assert set(out).issubset(BETA)
    return out


def main() -> None:
    word = BETA * 5
    assert len(word) == 20
    counts = {"commute": 0, "braid": 0, "cancel": 0}
    for turn, (action, pos) in enumerate(OPS, start=1):
        old_length = len(word)
        word = apply(word, action, pos)
        assert len(word) == old_length - (2 if action == "cancel" else 0)
        counts[action] += 1
        print(f"{turn:02d} {action:7s} @{pos:02d} -> {''.join(map(str, word)) or 'IDENTITY'}")
    assert len(OPS) == 35
    assert counts == {"commute": 15, "braid": 10, "cancel": 10}
    assert word == ()
    print("PASS: Y443 JMD beta^5=1 by 35 explicit presentation-valid Coxeter rewrites")


if __name__ == "__main__":
    main()
