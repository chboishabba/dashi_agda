#!/usr/bin/env python3
"""Finite differential of N21 gamma zero-prefix physical scanner.

Checks only the source scanZeros zero-prefix stage, not payload
decoding, a full N21 compiler, or Agda kernel acceptance.
"""
from dataclasses import dataclass
import random

B0, B1, BLANK, MARK = "B0", "B1", "Blank", "Mark"

SYMBOLS = (B0, B1, BLANK, MARK)
# Shape matches Agda TableProgram: OUTER indexed by input head,
# INNER indexed by work head; neither dimension may be transposed.
INPUT_ACTIONS = (
    ("skip-zero", B0, "right", MARK, "right", False),
    ("separator", B1, "stay", BLANK, "stay", True),
    ("end-blank", BLANK, "stay", BLANK, "stay", True),
    ("end-mark", MARK, "stay", BLANK, "stay", True),
)
LITERAL_TABLE = tuple(tuple(action for _ in SYMBOLS)
                      for action in INPUT_ACTIONS)


def dispatch(input_head, work_head):
    return LITERAL_TABLE[SYMBOLS.index(input_head)][SYMBOLS.index(work_head)]


@dataclass(frozen=True)
class Tape:
    left: tuple[str, ...]
    head: str
    right: tuple[str, ...]

    @property
    def count(self):
        return 1 + len(self.left) + len(self.right)


def encode(bits):
    return tuple(B1 if x else B0 for x in bits)


def scan_start(bits):
    digits = encode(bits)
    return Tape((), digits[0], digits[1:]) if digits else Tape((), BLANK, ())


def step(source: Tape, tally: Tape):
    # Exact four-row local input transition table, tally-head independent.
    action = dispatch(source.head, tally.head)
    if action[0] == "skip-zero":
        nxt = Tape((B0,) + source.left,
                   source.right[0] if source.right else BLANK,
                   source.right[1:] if source.right else ())
        marks = Tape((MARK,) + tally.left, BLANK, ())
        return nxt, marks, False
    return source, tally, True


def source_prefix(bits):
    k = 0
    for bit in bits:
        if bit:
            return k
        k += 1
    return None


def check_case(bits):
    source = scan_start(bits)
    tally = Tape((), BLANK, ())
    initial_size = source.count + tally.count
    instructions = 0
    while True:
        old_size = source.count + tally.count
        source, tally, halted = step(source, tally)
        instructions += 1
        assert source.count + tally.count <= old_size + 2
        assert source.count + tally.count <= initial_size + 2 * instructions
        if halted:
            break
        assert instructions <= len(bits)
    expected = source_prefix(bits)
    assert instructions == (expected + 1 if expected is not None else len(bits) + 1)
    assert len(tally.left) == (expected if expected is not None else len(bits))
    if expected is not None:
        assert source.head == B1
        assert source.left == (B0,) * expected
        assert source.right == encode(bits[expected + 1:])
        assert tally.left == (MARK,) * expected
    else:
        assert source.head == BLANK
    return instructions


def main():
    rng = random.Random(20261112)
    for input_head in SYMBOLS:
        for work_head in SYMBOLS:
            assert dispatch(input_head, work_head) == INPUT_ACTIONS[SYMBOLS.index(input_head)]
    # Regression catches the historical transposed-table bug: B0
    # with an initially blank tally tape MUST advance, never halt.
    assert dispatch(B0, BLANK)[0] == "skip-zero"
    cases = instructions = 0
    for zeros in range(257):
        for payload_size in (0, 1, 2, 3, 7, 16, 63):
            tail = tuple(bool(rng.getrandbits(1)) for _ in range(payload_size))
            instructions += check_case((False,) * zeros + (True,) + tail)
            cases += 1
    for _ in range(20000):
        zeros = rng.randrange(128)
        tail_size = rng.randrange(60)
        tail = tuple(bool(rng.getrandbits(1)) for _ in range(tail_size))
        valid = bool(rng.getrandbits(1))
        bits = (False,) * zeros + ((True,) if valid else ()) + (tail if valid else ())
        instructions += check_case(bits)
        cases += 1
    print(f"PASS physical gamma prefix: {cases:,} cases; {instructions:,} literal instructions")
    print("Finite source model only, not Agda or a full N21 compiler")

if __name__ == "__main__":
    main()
