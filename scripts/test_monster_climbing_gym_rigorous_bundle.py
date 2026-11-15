#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "rigorous_bundle",
    HERE / "monster_climbing_gym_verify_rigorous_bundle.py",
)
assert SPEC and SPEC.loader
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def test_exact_cell_inference() -> None:
    lo = mod.dyadic_endpoint("9", "-4")
    hi = mod.dyadic_endpoint("10", "-4")
    assert mod.inferred_unique_cell(lo, hi, 2) == 1

    boundary_lo = mod.dyadic_endpoint("8", "-4")
    assert mod.inferred_unique_cell(boundary_lo, hi, 2) is None


def test_synthetic_bundle() -> None:
    metadata = {
        "type": "metadata",
        "schema_version": "1.0.0",
        "producer": "synthetic-test-only",
        "external_producer_is_agda_proof": False,
    }
    row = {
        "type": "phase_certificate_candidate",
        "zero_index": 1,
        "prime": 2,
        "exponent": 1,
        "wall_n": 2,
        "precision_bits": 64,
        "zero_ordinate_interval": {
            "lower_mantissa": "14",
            "upper_mantissa": "15",
            "two_exp": "0",
        },
        "fractional_strip_unique": True,
        "phase_interval": {
            "lower_mantissa": "9",
            "upper_mantissa": "10",
            "two_exp": "-4",
        },
        "cell_unique": True,
        "cell_index": "1",
    }

    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "fixture.ndjson"
        p.write_text(json.dumps(metadata) + "\n" + json.dumps(row) + "\n")
        meta, rows = mod.load_ndjson(p)
        assert meta["producer"] == "synthetic-test-only"
        summary = mod.verify_rows(rows)
        assert summary["rows"] == 1
        assert summary["certified_rows"] == 1
        assert summary["unresolved_rows"] == 0
        assert summary["all_declared_cells_exact"] is True


def test_false_unique_claim_fails_closed() -> None:
    row = {
        "type": "phase_certificate_candidate",
        "zero_index": 1,
        "prime": 2,
        "exponent": 1,
        "wall_n": 2,
        "zero_ordinate_interval": {
            "lower_mantissa": "14",
            "upper_mantissa": "15",
            "two_exp": "0",
        },
        "fractional_strip_unique": True,
        "phase_interval": {
            "lower_mantissa": "8",
            "upper_mantissa": "9",
            "two_exp": "-4",
        },
        "cell_unique": True,
        "cell_index": "1",
    }
    summary = mod.verify_rows([row])
    assert summary["all_declared_cells_exact"] is False
    assert summary["failures"]


if __name__ == "__main__":
    test_exact_cell_inference()
    test_synthetic_bundle()
    test_false_unique_claim_fails_closed()
    print("PASS rigorous dyadic bundle verifier synthetic regression")
