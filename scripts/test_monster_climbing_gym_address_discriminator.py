#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "address_discriminator",
    HERE / "monster_climbing_gym_address_discriminator.py",
)
assert SPEC and SPEC.loader
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def test_occupancy_conserves_count() -> None:
    xs = [0.01, 0.11, 0.29, 0.49, 0.51, 0.99]
    counts = mod.occupancy_counts(xs, 5)
    assert len(counts) == 5
    assert sum(counts) == len(xs)


def test_uniform_fixture_has_zero_pearson() -> None:
    assert mod.pearson_uniform([2, 2, 2, 2]) == 0.0


def test_balanced_assignment_count() -> None:
    scores = {p: float(i) for i, p in enumerate(mod.ALL_PRIMES)}
    receipt = mod.exhaustive_label_test(scores)
    assert receipt["assignment_count"] == 15504
    assert 0 <= receipt["two_sided_tail_count"] <= 15504
    assert 0.0 <= receipt["two_sided_tail_fraction"] <= 1.0


if __name__ == "__main__":
    test_occupancy_conserves_count()
    test_uniform_fixture_has_zero_pearson()
    test_balanced_assignment_count()
    print("PASS native-address discriminator regression")
