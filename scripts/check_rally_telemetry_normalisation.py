#!/usr/bin/env python3
"""Regression check for the rally telemetry canonical normalizer."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NORMALIZER = ROOT / "scripts" / "rally_telemetry_normalize.py"
FIXTURE = ROOT / "scripts" / "data" / "rally_recce" / "telemetry_normalisation_fixture.jsonl"

EXPECTED_SIGNALS = {
    "simulationTime",
    "steeringInput",
    "throttleInput",
    "brakeInput",
    "engineSpeed",
    "wheelSpeed",
    "suspensionPosition",
    "renderedFrame",
}


def main() -> int:
    with tempfile.TemporaryDirectory() as td:
        out = Path(td) / "normalised.jsonl"
        receipt = Path(td) / "receipt.json"
        subprocess.run(
            [sys.executable, str(NORMALIZER), str(FIXTURE), str(out), "--receipt", str(receipt)],
            check=True,
            cwd=ROOT,
        )

        rows = [json.loads(line) for line in out.read_text(encoding="utf-8").splitlines() if line]
        rec = json.loads(receipt.read_text(encoding="utf-8"))

        assert len(rows) == 8
        assert {row["canonical_signal"] for row in rows} == EXPECTED_SIGNALS
        assert rec["sample_count"] == 8
        assert rec["canonical_signals"] == sorted(EXPECTED_SIGNALS)
        assert rec["source_provenance_retained"] is True
        assert rec["clock_lineage_retained"] is True
        assert rec["privileged_truth_promoted"] is False
        assert rec["claims_exact_cross_clock_synchronisation"] is False
        assert rec["claims_physical_truth"] is False

        for row in rows:
            assert "source_receipt" in row
            assert row["source_receipt"]["provenance_reference"] == "synthetic regression fixture"
            assert row["canonical_station_reference"] == "1034.2"

    print("rally telemetry normalisation fixture: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
