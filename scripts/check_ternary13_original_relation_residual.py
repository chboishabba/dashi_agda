#!/usr/bin/env python3
"""Finite executable regression for the original 12x12 relation -> 13+131 split.

Checks *algorithmic* 144-cell data preservation and the critical omitted
(1,0) counterexample. This does NOT replace Agda kernel typechecking.
The 13 observed cells are (i,i), i=0..11 and directed (0,1).
"""
from __future__ import annotations
from itertools import product
from pathlib import Path
import re
import sys

N = 12
CELLS = tuple(product(range(N), repeat=2))
OBSERVED = tuple((i, i) for i in range(N)) + ((0, 1),)
OMITTED = tuple(cell for cell in CELLS if cell not in OBSERVED)
assert len(CELLS) == 144 and len(OBSERVED) == 13 and len(OMITTED) == 131

def coarse(field: dict[tuple[int, int], int]) -> tuple[int, ...]:
    return tuple(field[cell] for cell in OBSERVED)

def residual(field: dict[tuple[int, int], int]) -> dict[tuple[int, int], int]:
    return {cell: 0 if cell in OBSERVED else field[cell] for cell in CELLS}

def reopen(code: tuple[int, ...], rest: dict[tuple[int, int], int]) -> dict[tuple[int, int], int]:
    values = dict(rest)
    values.update(zip(OBSERVED, code))
    return values

def check(field: dict[tuple[int, int], int]) -> None:
    code, rest = coarse(field), residual(field)
    assert reopen(code, rest) == field
    assert coarse(reopen(code, rest)) == code
    assert residual(reopen(code, rest)) == rest
    assert all(rest[cell] == 0 for cell in OBSERVED)

def run() -> int:
    zero = dict.fromkeys(CELLS, 0)
    check(zero)
    count = 1
    # Exhaustively probe each trit at each independent source address.
    for cell in CELLS:
        for trit in (-1, 0, 1):
            field = zero.copy()
            field[cell] = trit
            check(field)
            count += 1
    # For any valid code/residual pair, each inverse has the advertised result.
    for trit in (-1, 0, 1):
        for cell in CELLS:
            code = tuple(trit if address == cell else 0 for address in OBSERVED)
            rest = {address: trit if address == cell and address in OMITTED else 0 for address in CELLS}
            field = reopen(code, rest)
            assert coarse(field) == code
            assert residual(field) == rest
            count += 1
    reverse = zero.copy()
    reverse[(1, 0)] = 1
    assert coarse(zero) == coarse(reverse)
    assert residual(zero) != residual(reverse)
    assert reopen(coarse(reverse), residual(reverse)) == reverse
    print(f"PASS: {count} exact basis/inverse checks; 144 cells = 13 observed + 131 residual")
    print("PASS: directed (1,0) collision distinguished only by residual")
    return 0

if __name__ == "__main__":
    sys.exit(run())
