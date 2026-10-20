#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

SPEC = importlib.util.spec_from_file_location(
    "bundle_to_agda",
    HERE / "monster_climbing_gym_rigorous_bundle_to_agda.py",
)
assert SPEC and SPEC.loader
mod = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)


def synthetic_bundle(path: Path) -> None:
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
    path.write_text(json.dumps(metadata) + "\n" + json.dumps(row) + "\n")


def test_compile_synthetic_certificate() -> None:
    with tempfile.TemporaryDirectory() as td:
        bundle = Path(td) / "fixture.ndjson"
        synthetic_bundle(bundle)
        text, emitted, skipped = mod.compile_module(
            bundle,
            "DASHI.Moonshine.Generated.TestRigorousPhaseCertificates",
            "synthetic-version",
        )
        assert emitted == 1
        assert skipped == 0
        assert "certificate-z1-p2-a1" in text
        assert "Dyadic.certified-dyadic-radix-cell" in text
        assert "16 <? 18" in text
        assert "20 <? 32" in text
        assert "external enclosure remains provenance-bearing input" in text


if __name__ == "__main__":
    test_compile_synthetic_certificate()
    print("PASS rigorous bundle -> Agda compiler synthetic regression")
