#!/usr/bin/env python3
"""Exact finite model for all source directional 2x3 window constructors.

Checks that the two *centered-context* boundary guards introduced in
ConcreteTapeAfterUniqueFromLocalityExact suffice for 1-head preservation
for every single-symbol, single-state row of length 3..12 and every move
direction. Explicitly finds unguarded counterexamples. This is bounded
differential mathematics, NOT an Agda typecheck or universal proof.
"""
from itertools import product
from pathlib import Path

P, H = 0, 1

def legal(direction, old, new):
    if old == (P, P, P) and new == (P, P, P):
        return "unchanged"
    cases = {
        "left": {
            ((P, H, P), (H, P, P)): "center",
            ((P, P, P), (P, P, H)): "minus-two",
            ((P, P, H), (P, H, P)): "minus-one",
            ((H, P, P), (P, P, P)): "plus-one",
        },
        "stay": {
            ((P, H, P), (P, H, P)): "center",
            ((P, P, H), (P, P, H)): "minus-one",
            ((H, P, P), (H, P, P)): "plus-one",
        },
        "right": {
            ((P, H, P), (P, P, H)): "center",
            ((P, P, H), (P, P, P)): "minus-one",
            ((H, P, P), (P, H, P)): "plus-one",
            ((P, P, P), (H, P, P)): "plus-two",
        },
    }
    return cases[direction].get((old, new))


def assert_source_contract() -> None:
    root = Path(__file__).resolve().parents[1]
    base = root / "DASHI/Mathematics/Complexity"
    patterns = (base / "ConcreteTapeLocalWindowPatternsExact.agda").read_text()
    guarded = (base / "ConcreteTapeAfterUniqueFromLocalityExact.agda").read_text()
    step = (base / "ConcreteTapeDecodedTransitionStepExact.agda").read_text()
    for old in (
        "legalOldLeftPlainForcesNewLeftPlain :",
        "legalOldRightPlainForcesNewRightPlain :",
    ):
        assert old not in patterns, f"unsound universal plainness lemma resurfaced: {old}"
    assert "data LegalWindowForRule\n    (machine" in patterns
    assert "record NoGhostContextBoundaries" in guarded
    assert "NoGhostContextBoundaries scan interior" in guarded
    assert "AfterUnique.NoGhostContextBoundaries" in step
    assert "localityAfterUniqueDerivedPaid = false" in step
    assert "oneSATTimeSliceToMachineStepPaid = false" in step


def main() -> int:
    assert_source_contract()
    accepted = 0
    unguarded_ghosts = 0
    guarded_ghosts = 0
    for length in range(3, 13):
        for head in range(1, length - 1):
            old = tuple(int(i == head) for i in range(length))
            for direction in ("left", "stay", "right"):
                for after in product((P, H), repeat=length):
                    windows = [
                        legal(direction, old[i:i + 3], after[i:i + 3])
                        for i in range(length - 2)
                    ]
                    if any(w is None for w in windows):
                        continue
                    if windows[head - 1] != "center":
                        continue
                    accepted += 1
                    before_center_prefix_length = head - 1
                    after_prefix = after[:before_center_prefix_length]
                    after_suffix = after[head + 2:]
                    front = not after_prefix or after_prefix[0] == P
                    end = not after_suffix or after_suffix[-1] == P
                    if after.count(H) != 1:
                        unguarded_ghosts += 1
                        if front and end:
                            guarded_ghosts += 1
                            raise AssertionError(
                                (length, head, direction, old, after, windows)
                            )
    assert unguarded_ghosts > 0
    assert guarded_ghosts == 0
    print(f"PASS: {accepted} exhaustive legal centered row pairs (length 3..12).")
    print(f"PASS: {unguarded_ghosts} unguarded ghost rows found.")
    print("PASS: 0 false-after-uniqueness rows survive both centered end guards.")
    print("NOT a universal Agda kernel receipt or SAT boundary-CNF certificate.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
