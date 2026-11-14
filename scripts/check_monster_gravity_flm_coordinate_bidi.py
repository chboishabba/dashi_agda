#!/usr/bin/env python3
"""Independent exhaustive oracle for the Phase-P0 typed sector-label inverse.

This is a finite-index regression, not an Agda kernel proof and not a
Monster-equivariant/physical-field intertwiner.
"""
from collections import Counter

GRAVITY_COUNTS = {"dilaton": 1, "metric": 299, "pform": 98280, "twisted": 98304}
FLM_COUNTS = {"sym2": 300, "norm4": 98280, "twisted": 98304}

def to_flm(label):
    sector, i = label
    if sector == "dilaton":
        assert i == 0
        return ("sym2", 0)
    if sector == "metric":
        return ("sym2", i + 1)
    if sector == "pform":
        return ("norm4", i)
    if sector == "twisted":
        return ("twisted", i)
    raise ValueError(label)

def to_gravity(label):
    sector, i = label
    if sector == "sym2":
        return ("dilaton", 0) if i == 0 else ("metric", i - 1)
    if sector == "norm4":
        return ("pform", i)
    if sector == "twisted":
        return ("twisted", i)
    raise ValueError(label)

def check():
    assert sum(GRAVITY_COUNTS.values()) == 196884
    assert sum(FLM_COUNTS.values()) == 196884
    images = set()
    for sector, size in GRAVITY_COUNTS.items():
        for i in range(size):
            x = sector, i
            y = to_flm(x)
            assert 0 <= y[1] < FLM_COUNTS[y[0]], (x, y)
            assert to_gravity(y) == x, x
            assert y not in images, y
            images.add(y)
    for sector, size in FLM_COUNTS.items():
        for i in range(size):
            y = sector, i
            assert y in images, y
            assert to_flm(to_gravity(y)) == y, y
    counts = Counter(sector for sector, _ in images)
    assert counts == FLM_COUNTS, counts
    print("PASS: 196884/196884 gravity→FLM→gravity, 196884/196884 FLM→gravity→FLM")
    print("PASS: sector census", dict(sorted(counts.items())))
    print("BOUNDARY: pure coordinate-label bijection; no physical or VOA intertwiner")

if __name__ == "__main__":
    check()
