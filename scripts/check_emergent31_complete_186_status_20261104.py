#!/usr/bin/env python3
"""Exact P00–P11 lemma and status-appendix reconciliation for #1460.

Each original canonical ID must occur once in a checklist statement and
once in the second *status* table; this must NOT be interpreted as 372
distinct lemmas. Fail closed if owners/IDs drift, appendices omit a
statement, or an item is marked physically complete without an explicitly
audited certificate. This is a source/document consistency check only,
NOT Agda kernel acceptance or proof of physical existence.
"""
from collections import Counter
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
DEFAULT = ROOT / "Docs/roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md"
GROUP_COUNTS = {
    "P00": 10, "P01": 19, "P02": 16, "P03": 14,
    "P04": 12, "P05": 16, "P06": 20, "P07": 16,
    "P08": 17, "P09": 13, "P10": 14, "P11": 19,
}
CANONICAL = re.compile(
    r"^- \[[ x]\] \*\*(P(?:0[0-9]|1[01])\.L[0-9]{2})\*\* (.+)$",
    re.MULTILINE,
)
STATUS = re.compile(
    r"^\| \x60(P(?:0[0-9]|1[01])\.L[0-9]{2})\x60 \| (.+?) \| (.+?) \|$",
    re.MULTILINE,
)


def audit(markdown: str) -> None:
    canonical = CANONICAL.findall(markdown)
    status = STATUS.findall(markdown)
    canonical_ids = [k for k, _ in canonical]
    status_ids = [k for k, _, _ in status]
    assert len(canonical_ids) == 186, f"canonical count {len(canonical_ids)} != 186"
    assert len(status_ids) == 186, f"status count {len(status_ids)} != 186"
    assert len(set(canonical_ids)) == 186, "duplicate canonical IDs"
    assert len(set(status_ids)) == 186, "duplicate status IDs"
    assert set(canonical_ids) == set(status_ids), (
        f"missing in appendix: {sorted(set(canonical_ids)-set(status_ids))}; "
        f"extra in appendix: {sorted(set(status_ids)-set(canonical_ids))}"
    )
    actual_counts = Counter(k.split(".")[0] for k in canonical_ids)
    assert dict(actual_counts) == GROUP_COUNTS, (
        f"group distribution changed: {dict(actual_counts)}"
    )
    for id_, owner, state in status:
        assert owner.strip(), f"missing owner {id_}"
        assert "kernel unverified / physical open" in state, (
            f"physical/kernel promotion needs an independent certificate: {id_}"
        )
        if id_.startswith(("P05.", "P06.")):
            assert "YM #1444" in owner, f"YM parent ownership changed {id_}"
    print("PASS: 186 distinct canonical lemma statements, exactly")
    print("      186 matching status rows, 12 programme groups and owner splits")
    print("      SOURCE / KERNEL / PHYSICAL separation preserved; proof remains OPEN")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("roadmap", nargs="?", type=Path, default=DEFAULT)
    args = parser.parse_args()
    audit(args.roadmap.read_text(encoding="utf-8"))
