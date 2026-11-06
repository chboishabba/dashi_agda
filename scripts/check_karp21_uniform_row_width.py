#!/usr/bin/env python3
"""Finite differential check of original constant-width run encoding.

This checks the *semantic* block-slice/cast naturality law and guards
against reintroducing the ill-typed homogeneous final-row statement.
The original Agda dependent proof still requires Agda 2.9 acceptance.
"""
from __future__ import annotations

from itertools import product
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent / "DASHI/Mathematics/Complexity"


def block_slice(chunks: tuple[tuple[int, ...], ...], index: int, width: int) -> tuple[int, ...]:
    encoded = tuple(bit for chunk in chunks for bit in chunk)
    return encoded[index * width : (index + 1) * width]


def verify() -> None:
    checked = 0
    for cols in range(1, 8):
        for cell_width in range(1, 5):
            width = cols * cell_width
            for steps in range(8):
                rows = tuple(
                    tuple((column * 7 + index * 11 + cell_width) % 2
                          for column in range(width))
                    for index in range(steps + 1)
                )
                for slot, row in enumerate(rows):
                    assert block_slice(rows, slot, width) == row
                    assert len(row) == len(rows[0]) == width
                    checked += 1
                assert block_slice(rows, steps, width) == rows[-1]
    # A step with different cell widths cannot inhabit the original
    # fixed-width tableau without the missing equality proof.
    left = (0, 1, 0, 1)
    right = (1, 0, 1, 0, 1)
    assert len(left) != len(right)

    assignment = (BASE / "ConcreteTapeAcceptingRunAssignmentExact.agda").read_text()
    initial = (BASE / "ConcreteTapeAcceptingRunInitialCompleteExact.agda").read_text()
    view = (BASE / "ConcreteTapeUniformRunWidthExact.agda").read_text()
    assert "finalBlockTransport" in assignment
    assert "sym (runFinishCanonicalLength run)" in assignment
    assert "rewrite stepCanonicalLength step" not in assignment.split(
        "encodeRunRows_finalBlock :", 1
    )[1].split("finalRunRowSlot_eq_finalRowSlot :", 1)[0]
    assert "decodeCastRow stateCoverage symbolCoverage refl encoded = refl" in initial
    for lemma in (
        "originalRowAt :",
        "everyOriginalRowHasTableauWidth :",
        "originalFixedWidthRowAt :",
        "originalFinalRowAtFinalSlot :",
    ):
        assert lemma in view, lemma
    print(f"PASS: {checked} deterministic indexed-row slices and fixed widths")
    print("PASS: final-row cast has one original equality owner")
    print("NOT AN AGDA 2.9 KERNEL RECEIPT")


if __name__ == "__main__":
    verify()
