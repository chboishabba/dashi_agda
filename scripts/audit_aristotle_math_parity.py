#!/usr/bin/env python3
from __future__ import annotations
import csv
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "third_party" / "aristotle_math_369"
ALLOWED = {
    "near-core-parity", "substantial-core", "partial", "minimal-partial",
    "unported-core", "unported", "aggregate-only",
}

def rows(name: str):
    with (BASE / name).open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f, delimiter="\t"))

def main() -> None:
    source = rows("SOURCE_MANIFEST.tsv")
    decl = rows("DECLARATION_MANIFEST.tsv")
    parity = rows("PARITY_MANIFEST.tsv")
    assert len(source) == 18, f"expected 18 source modules, found {len(source)}"
    assert len(decl) == 409, f"expected 409 named declarations, found {len(decl)}"
    source_names = [r["module"] for r in source]
    assert len(source_names) == len(set(source_names)), "duplicate source module"
    parity_names = [r["source_module"] for r in parity]
    assert len(parity_names) == len(set(parity_names)), "duplicate parity module"
    assert set(source_names) == set(parity_names), "source/parity module mismatch"
    assert all(r["status"] in ALLOWED for r in parity), "unknown parity status"
    per_decl = {}
    for r in decl:
        per_decl[r["module"]] = per_decl.get(r["module"], 0) + 1
    for r in source:
        expected = int(r["declarations"])
        actual = per_decl.get(r["module"], 0)
        assert expected == actual, f"{r['module']}: declaration count {actual} != {expected}"
    assert any(r["status"] in {"unported", "unported-core"} for r in parity), (
        "ledger unexpectedly claims complete parity"
    )
    readme = (BASE / "README.md").read_text(encoding="utf-8")
    assert "Aristotle (Harmonic)" in readme
    assert "Co-authored-by: Aristotle (Harmonic)" in readme
    print("Aristotle math parity ledger: 18 modules / 409 declarations; fail-closed statuses valid")

if __name__ == "__main__":
    main()
