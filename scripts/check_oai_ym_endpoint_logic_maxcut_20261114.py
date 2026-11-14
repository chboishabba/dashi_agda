#!/usr/bin/env python3
"""Finite logic regression for October OAI YM A7/A8 witness separation.

A synthetically distinct accepted witness and OPE witness do not imply
a single shared witness. The test does not model Yang--Mills physics and
is not a Lean or Agda kernel proof.
"""
from itertools import product
import json


def independent(p, q):
    return any(p) and any(q)


def joint(p, q):
    return any(a and b for a, b in zip(p, q))


def source_transfer(p, q):
    return all((not a) or b for a, b in zip(p, q))


def main():
    ps = list(product((False, True), repeat=2))
    disagreements = 0
    for p in ps:
        for q in ps:
            assert not joint(p, q) or independent(p, q)
            if source_transfer(p, q) and any(p):
                assert joint(p, q)
            if independent(p, q) and not joint(p, q):
                disagreements += 1
    a7, a8 = (True, False), (False, True)
    assert independent(a7, a8) and not joint(a7, a8)
    assert any(a8) and not all(a8)
    print(json.dumps({
        "status": "PASS",
        "predicate_pairs": 16,
        "independent_but_not_joint_models": disagreements,
        "same_witness_transfer_regression": True,
        "positive_probe_not_uniform_gap_regression": True,
        "native_kernel_checked": False,
        "YM_E1_D1_D2_mass_gap_proved": False
    }, sort_keys=True))


if __name__ == "__main__":
    main()
