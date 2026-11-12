#!/usr/bin/env python3
"""Finite differential of the selected Karp21NativeBitTapePhysicalMachineExact zipper.
Source-aligned tests, NOT an Agda acceptance receipt or N21 compiler proof.
"""
from dataclasses import dataclass
from itertools import product
import random

CELLS = ("B0", "B1", "Blank", "Mark")
DIRECTIONS = ("left", "right", "stay")

@dataclass(frozen=True)
class Tape:
    left: tuple[str, ...]
    head: str
    right: tuple[str, ...]

    @property
    def cells(self) -> int:
        return 1 + len(self.left) + len(self.right)

def write(symbol: str, t: Tape) -> Tape:
    return Tape(t.left, symbol, t.right)

def walk(direction: str, t: Tape) -> Tape:
    if direction == "stay":
        return t
    if direction == "left":
        if not t.left:
            return Tape((), "Blank", (t.head,) + t.right)
        return Tape(t.left[1:], t.left[0], (t.head,) + t.right)
    if direction == "right":
        if not t.right:
            return Tape((t.head,) + t.left, "Blank", ())
        return Tape((t.head,) + t.left, t.right[0], t.right[1:])
    raise ValueError(direction)

@dataclass(frozen=True)
class Configuration:
    state: int
    source: Tape
    work: tuple[Tape, ...]
    halted: bool

    @property
    def cells(self) -> int:
        return self.source.cells + sum(t.cells for t in self.work)

def program(state: int, heads: tuple[str, ...], q: int):
    """Selected deterministic local table; no full-tape inspection."""
    rank = state + sum(CELLS.index(h) * (i + 1) for i, h in enumerate(heads))
    writes = tuple(CELLS[(rank + i) % 4] for i in range(len(heads)))
    moves = tuple(DIRECTIONS[(rank + i) % 3] for i in range(len(heads)))
    return (rank % q, writes, moves, rank % 17 == 0)

def step(c: Configuration, q: int) -> Configuration:
    if c.halted:
        return c
    heads = (c.source.head,) + tuple(t.head for t in c.work)
    state, writes, moves, halt = program(c.state, heads, q)
    tapes = (c.source,) + c.work
    nxt = tuple(walk(move, write(symbol, tape))
                for move, symbol, tape in zip(moves, writes, tapes))
    return Configuration(state, nxt[0], nxt[1:], halt)

def word_tape(bits: tuple[bool, ...]) -> Tape:
    if not bits:
        return Tape((), "Blank", ())
    return Tape((), "B1" if bits[0] else "B0",
                tuple("B1" if b else "B0" for b in bits[1:]))

def main() -> None:
    rng = random.Random(20261112)
    checked = 0
    for n_left in range(4):
        for n_right in range(4):
            for l in product(CELLS, repeat=n_left):
                for r in product(CELLS, repeat=n_right):
                    for h in CELLS:
                        t = Tape(l, h, r)
                        for w in CELLS:
                            assert write(w, t).cells == t.cells
                            for direction in DIRECTIONS:
                                new = walk(direction, write(w, t))
                                assert new.cells <= t.cells + 1
                                checked += 1
                        if l:
                            assert walk("right", walk("left", t)) == t
                        if r:
                            assert walk("left", walk("right", t)) == t
    # Explicitly enumerate all q * 4^(k+1) finite table entries,
    # independent of the cursor/tape tail contents.
    q, work_count = 3, 2
    table = {(state, heads): program(state, heads, q)
             for state in range(q)
             for heads in product(CELLS, repeat=work_count + 1)}
    assert len(table) == q * (4 ** (work_count + 1))
    for (state, heads), command in table.items():
        assert command == program(state, heads, q)
        checked += 1
    for width in (0, 1, 2, 4):
        for _ in range(4000):
            bit_len = rng.randrange(24)
            bits = tuple(bool(rng.randrange(2)) for _ in range(bit_len))
            tape = word_tape(bits)
            assert tape.cells == max(1, len(bits))
            config = Configuration(rng.randrange(11), tape,
                tuple(Tape((), "Blank", ()) for _ in range(width)), False)
            initial = config.cells
            fuel = rng.randrange(32)
            for i in range(fuel):
                next_config = step(config, 11)
                assert next_config.cells <= config.cells + width + 1
                config = next_config
                assert config.cells <= initial + (i + 1) * (width + 1)
            checked += fuel + 1
    print(f"Physical tape finite differential PASS: {checked:,} checks")
    print("Source-model regression only; no Agda or N21 compilation receipt")

if __name__ == "__main__":
    main()
