from __future__ import annotations

import importlib.util
import math
import sys
from pathlib import Path

MODULE_PATH = Path(__file__).resolve().parents[1] / "rsa_ssp_fibre_separation_benchmark.py"
SPEC = importlib.util.spec_from_file_location("rsa_ssp_bench", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
bench = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = bench
SPEC.loader.exec_module(bench)


def test_local_product_compatibility_is_constant_on_units() -> None:
    n = 77
    basis = (3, 5, 7, 11, 13)
    candidates = (2, 4, 8, 16, 17, 19)
    scores = [bench.product_compatible_score(x, n, basis) for x in candidates]
    assert scores == [1.0] * len(candidates)


def test_no_factor_search_methods_are_declared() -> None:
    assert bench.SEARCH_METHODS_USED == ()
    assert "sqrt-window-ordering" in bench.FORBIDDEN_SEARCH_METHODS
    assert "private-factor-oracle-in-scoring" in bench.FORBIDDEN_SEARCH_METHODS


def test_deterministic_smoke_is_fail_closed() -> None:
    bits = (32, 36, 40)
    rows = bench.run_suite(bits, trials=4, distractors=40, seed=20260518)
    receipt = bench.summarize(
        rows,
        seed=20260518,
        bits_list=bits,
        trials=4,
        distractors=40,
    )
    decision = receipt["decision"]
    assert decision["unbiased_factor_signal_observed"] is False
    assert decision["general_rsa_break_promoted"] is False
    assert decision["unbiased_product_compatibility_is_chance"] is True
    assert decision["verdict"] in {
        "structured-source-detector-only",
        "baseline-equivalent",
    }


def test_product_compatibility_auc_is_exactly_chance() -> None:
    bits = (32, 36)
    rows = bench.run_suite(bits, trials=3, distractors=30, seed=36915)
    receipt = bench.summarize(
        rows,
        seed=36915,
        bits_list=bits,
        trials=3,
        distractors=30,
    )
    observed = receipt["summary"]["unbiased"]["SSP15"][
        "auc_product_compatible_mean"
    ]
    assert math.isclose(observed, 0.5, abs_tol=1e-12)
