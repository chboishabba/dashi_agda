#!/usr/bin/env python3
"""Exact Z3 cutoff-4 original R846/R848 zero-support adversarial test.

This is an independent finite arithmetic regression of the ORIGINAL six-mode
Snapshot.velocityActive, Actual Physical.modeWithinCutoff 4 and
Snapshot.forcingActive classification. It is NOT an Agda kernel receipt
or a proof of Navier-Stokes regularity.

The original physicalTriadEnumeration 4 uses 9^3=729 lattice modes as
p and q, with resonance k=p+q and output |k_i|<=4.  It DOES include
zero output and the six selected p=-q pairs.
"""
from collections import Counter
from itertools import product

SEEDS = [
    (-3, -4, 0), (-3, 0, 0), (0, -4, 0),
    (0, 4, 0), (3, 0, 0), (3, 4, 0)
]
ACTUAL_FORCING_SUPPORT = {
    (-3, -4, 0), (-3, 0, 0), (-3, 4, 0), (0, -4, 0),
    (0, 4, 0), (3, -4, 0), (3, 0, 0), (3, 4, 0)
}
ZERO = (0, 0, 0)


def add(p, q):
    return tuple(x + y for x, y in zip(p, q))


def within(k):
    return all(abs(x) <= 4 for x in k)


def main():
    assert len(SEEDS) == len(set(SEEDS)) == 6
    assert all(within(mode) for mode in SEEDS)
    source_pairs = [(p, q, add(p, q)) for p, q in product(SEEDS, repeat=2)]
    actual_cutoff = [triple for triple in source_pairs if within(triple[2])]
    counts = Counter(k for _, _, k in actual_cutoff)

    assert len(source_pairs) == 36
    assert len(actual_cutoff) == 22
    assert counts[ZERO] == 6
    assert {k for k in counts if k != ZERO} == ACTUAL_FORCING_SUPPORT
    assert all(counts[k] == 2 for k in ACTUAL_FORCING_SUPPORT)
    assert counts[ZERO] > 0  # OLD R846 all-mode empty claim is FALSE

    # The full original ordered triad enumeration (before zero-field
    # pruning) also includes the actual six p=-q selected zero cells.
    # Per coordinate, (p,q) in [-4,4]^2 with |p+q|<=4 gives 61 choices.
    one_dimensional_valid = sum(9 - abs(k) for k in range(-4, 5))
    assert one_dimensional_valid == 61
    assert one_dimensional_valid ** 3 == 226981

    print("PASS: selected 36 source seed-pairs; 22 retained in cutoff 4")
    print("PASS: six selected zero-output incidences (old F1 counterexample)")
    print("PASS: all 16 nonzero incidences in exactly eight source forcing modes")
    print("PASS: 226981 full physical triads in 9^3 cutoff-cube convention")
    print("REPAIR: R436 handles output zero; original R848 handles nonzero")
    print("KERNEL: source-written, pinned local Agda 2.9 still required")


if __name__ == "__main__":
    main()
