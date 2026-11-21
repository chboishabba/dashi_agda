#!/usr/bin/env python3
"""Independent finite reference for TSVF single-branch macro-robustness Agda.

Original source is the finite history owner and selected-branch majority
analogue; this is NOT the 2014/2017 quantum-overlap N/n theorem, nor a
physical macroscopic time-reversal experiment, multiverse observation,
Agda kernel check, or emergent (3,1)/YM/OS theorem.
"""
from itertools import product

POINTERS = (0, 1)
FAULT_SITES = (0, 1, 2)
CHOICES = ("minus", "plus")

def encode(pointer: int) -> tuple[int, int, int]:
    return (pointer,) * 3

def flip_once(triple: tuple[int, int, int], site: int) -> tuple[int, int, int]:
    t = list(triple)
    t[site] = 1 - t[site]
    return tuple(t)

def macro_readout(triple: tuple[int, int, int]) -> int:
    return int(sum(triple) >= 2)

def past_record(choice: str) -> str:
    assert choice in CHOICES
    return "quiet"

def selected_macro(choice: str) -> int:
    return CHOICES.index(choice)

def original_hidden_history(choice: str) -> tuple[int, int]:
    # source owner stateZero -> stateMinus/statePlus, encoded as 0,-1/+1
    return (0, -1 if choice == "minus" else +1)

def reverse_history(history: tuple[int, int]) -> tuple[int, int]:
    a, b = history
    return (-b, -a)

def transition_cost(history: tuple[int, int]) -> int:
    a, b = history
    return abs(a - b)

def run() -> None:
    all_corrupted = {}
    for p, site in product(POINTERS, FAULT_SITES):
        original = encode(p)
        damaged = flip_once(original, site)
        assert damaged != original
        assert macro_readout(damaged) == p
        all_corrupted[(p, site)] = damaged
    assert macro_readout(flip_once(flip_once(encode(0), 0), 1)) == 1
    assert all_corrupted[(0, 0)] != all_corrupted[(0, 2)]
    assert macro_readout(all_corrupted[(0, 0)]) == macro_readout(all_corrupted[(0, 2)])
    # No function of this common macro value recovers two distinct fine records.
    assert past_record("minus") == past_record("plus")
    assert original_hidden_history("minus") != original_hidden_history("plus")
    assert selected_macro("minus") != selected_macro("plus")
    for choice, site in product(CHOICES, FAULT_SITES):
        assert macro_readout(flip_once(encode(selected_macro(choice)), site)) == selected_macro(choice)
    for a, b in product((-1, 0, +1), repeat=2):
        h = (a, b)
        assert reverse_history(reverse_history(h)) == h
        assert transition_cost(reverse_history(h)) == transition_cost(h)
    print("PASS: 6/6 one-fault macro restorations, every single flip changes fine data")
    print("PASS: sharp two-fault counterexample reverses the selected macro pointer")
    print("PASS: macro cannot recover two distinct corrupted microscopic encodings")
    print("PASS: original selected-branch past record fixed, hidden histories distinct")
    print("PASS: 9/9 reversible two-step histories and reversal-symmetric transition costs")
    print("NOTE: finite symbolic reference, not quantum ABL/macroscopic-time physics")

if __name__ == "__main__":
    run()
