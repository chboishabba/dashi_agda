#!/usr/bin/env python3
"""Regression contract for the predeclared native-address discriminator result."""

from pathlib import Path
import importlib.util

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SPEC = importlib.util.spec_from_file_location(
    "address_discriminator",
    HERE / "monster_climbing_gym_address_discriminator.py",
)
assert SPEC and SPEC.loader
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)

DISCOVERY = ROOT / "scripts" / "data" / "monster_climbing_gym_first_849_zeros.json"
HELD_OUT = ROOT / "scripts" / "data" / "monster_climbing_gym_zeros_850_1698.json"


def evaluate(path: Path):
    zeros = mod.load_zero_cache(path)
    rows = [mod.prime_standardized_score(zeros, p, shift_steps=720) for p in mod.ALL_PRIMES]
    scores = {int(row["prime"]): float(row["standardized_z"]) for row in rows}
    return rows, mod.exhaustive_label_test(scores)


def test_discovery_address_discriminator_is_not_tail_extreme() -> None:
    _, result = evaluate(DISCOVERY)
    assert abs(result["actual_contrast"] - (-0.4278031863279293)) < 1e-12
    assert result["assignment_count"] == 15504
    assert result["two_sided_tail_count"] == 7074
    assert 0.45 < result["two_sided_tail_fraction"] < 0.46


def test_held_out_address_discriminator_is_also_not_tail_extreme() -> None:
    _, result = evaluate(HELD_OUT)
    assert abs(result["actual_contrast"] - 0.23515611780682538) < 1e-12
    assert result["assignment_count"] == 15504
    assert result["two_sided_tail_count"] == 10449
    assert 0.67 < result["two_sided_tail_fraction"] < 0.68


if __name__ == "__main__":
    test_discovery_address_discriminator_is_not_tail_extreme()
    test_held_out_address_discriminator_is_also_not_tail_extreme()
    print("PASS native-address discriminator discovery/held-out result")
