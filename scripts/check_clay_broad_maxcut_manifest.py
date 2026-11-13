#!/usr/bin/env python3
"""Fail-closed semantic validator for the original six-Clay max-cut ledger.

This is a SOURCE/AUTHORITY audit. It never replaces Agda/Lean kernel checks,
original mathematical producers or selected physical/analytic receipts.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PATH = ROOT / "Docs/roadmaps/ClayBroadPRExactRemaining20261112.json"
PROBLEMS = {"NS", "RH", "PNP", "YM", "BSD", "HODGE"}
ALLOWED = {
    "new_mathematics", "source_weld", "formal_weld", "formalization",
    "analytic_source", "arithmetic_source", "verification", "integration"
}
FLAGS = (
    "source_written_gate", "local_checked_gate",
    "kernel_accepted_gate", "physical_or_integrated_gate"
)


def verify(document):
    assert document["original_clay_gates_solved_here"] == 0
    items = document["obligations"]
    ids = [item["id"] for item in items]
    assert len(ids) == len(set(ids)), "duplicate exact lemma ID"
    assert len(items) >= 30, "partial, silent dropped obligations"
    assert {x["problem"] for x in items} == PROBLEMS | {"SHARED"}
    classes = Counter()
    for item in items:
        assert item["id"] and item["source"] and item["next_smallest_action"]
        stage = item["gate_status"]
        assert stage in {
            "open", "source_written_kernel_pending", "partial_source_written"
        }, "unrecognized stage would silently promote gate"
        if stage != "open":
            # Only the two explicitly documented intermediate F19 source stages
            # may be source-written in this terminal-gate ledger.
            assert item["id"] in {
                "YM-P0-DE-ORIGINAL-F19", "YM-P0-F19-ORIGINAL-MARKS"
            }, "no new intermediate promotions without source/receipt review"
            assert item["source_written_gate"] is True
            assert item["kernel_accepted_gate"] is False
            assert item["physical_or_integrated_gate"] is False
        assert item["classification"] in ALLOWED
        assert "CI" not in str(item.get("kernel_receipt", "")), "CI is not local authority"
        assert all(type(item[k]) is bool for k in FLAGS)
        # A physical/semantic claim can never be promoted from a description,
        # an untested module or a standalone receipt queue.
        if item["physical_or_integrated_gate"]:
            assert item["kernel_accepted_gate"]
            assert item.get("physical_receipt")
        if item["kernel_accepted_gate"]:
            assert item["local_checked_gate"]
            assert item.get("kernel_receipt")
            assert item.get("kernel_commit")
        if item["local_checked_gate"]:
            assert item.get("local_receipt")
        if item["source_written_gate"]:
            assert item.get("source_commit")
        classes[item["classification"]] += 1
    for gate in ("E1", "D1", "D2", "N1", "G1"):
        assert any(x["problem"] == "YM" and x["gate"] == gate for x in items)
    for gate in ("A1", "A2/G3", "B"):
        assert any(x["problem"] == "RH" and x["gate"] == gate for x in items)
    assert any(x["id"] == "PNP-LOWER" for x in items)
    assert any(x["id"] == "HODGE-UNIV" for x in items)
    assert any(x["id"] == "BSD-K5" for x in items)
    return len(items), classes


if __name__ == "__main__":
    count, kinds = verify(json.loads(PATH.read_text(encoding="utf-8")))
    print("PASS: exact Clay max-cut gate ledger, IDs and proof-status firewall")
    print("Remaining/unaccepted exact producer rows:", count)
    print("Gate kinds:", dict(kinds))
    print("NO Clay endpoint or physical gate was promoted by this validator.")
    # Keep the original six-Clay terminal ledger and the broader eleven-lane
    # DONOR/consumer source audit in one default local referee. The latter is
    # deliberately non-authoritative: neither check compiles Agda/Lean.
    from check_dashi_all_lane_source_donors import (
        LEDGER as ALL_LANE_LEDGER, verify as verify_source_donors
    )
    report = verify_source_donors(
        json.loads(ALL_LANE_LEDGER.read_text(encoding="utf-8"))
    )
    print("PASS: separate eleven-lane source donor/bridge ledger", report)
    print("NO source-owner link or donor record is a kernel receipt.")

