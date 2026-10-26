#!/usr/bin/env python3
"""Reproducible, source-bounded GLOBAL cooling/CO2-plant claim audit.

The 18-row ledger was deliberately curated for original-source investigation.
It is NOT a worldwide random/probability sample. This tool must never output
a global fraction of denialism, a rank of "top deniers", or a fake count of
scientific studies from the repeated publication of claims.

Original authorship belongs to named journalists, scientists, publishers,
industry institutions and historians in the data; this classification and
the associated source-written verification are repo work, not their claims.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LEDGER = (
    ROOT / "Docs/support/reference/global_climate_denial_claim_genealogy_20261027.csv"
)
FIELDS = (
    "record_id", "claim_family", "proposition_variant", "source_date",
    "original_author_or_institution", "source_document", "source_locator",
    "source_object_id", "argument_root_family", "source_role",
    "relation_to_previous", "independent_empirical_origin",
    "attribution_and_nonpromotion_boundary",
)
# This is a typed SOURCE-ROLE lattice, not a hypothesis that all appearances
# of the same sentence came from a single original person.
CLAIM_FAMILIES = {
    "COOLING_1970S_MEDIA", "COOLING_1970S_CONSENSUS",
    "COOLING_1998_WINDOW", "COOLING_OBSERVED_GLOBAL",
    "CO2_PLANT_BENEFITS_PROMOTION", "CO2_FERTILIZATION_PHYSICAL",
    "CO2_FERTILIZATION_CONSTRAINTS", "GLOBAL_CLAIM_TAXONOMY",
}
# Positive same-original/response/campaign findings with documented scope.
# These directed pairs are not all source copies. Keep the asserted relation.
EDGES = (
    ("GC01", "GC02", "original-author-self-correction", "publisher+attributed-reprint"),
    ("GP01", "GP02", "named-sequel-same-industry-campaign", "archival-corroborated"),
    ("GP03", "GP05", "explicit-institutional-disavowal", "institution-original"),
    ("GP04", "GP06", "later-related-paper-not-byte-identical", "original-journal-metadata"),
)
# Equality of phrases is not a payment, source-copy, or first-author receipt.
UNPAID_TRANSMISSIONS = (
    ("GP01", "GP07", "No WFA-to-CO2 Coalition script/payment original"),
    ("GP01", "GP03", "No WFA-to-OISM specific commission original"),
    ("GP09", "GP07", "CO2 fertilization science is not a proven direct source copy"),
    ("GC01", "GC04", "1975 speculative media cooling not same original as 1998-window"),
)

def read_ledger(path: Path = DEFAULT_LEDGER) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        if reader.fieldnames != list(FIELDS):
            raise ValueError("Source ledger column schema changed")
        rows = list(reader)
    ids = [r["record_id"] for r in rows]
    if not rows or len(set(ids)) != len(ids):
        raise ValueError("Missing or duplicate original appearance IDs")
    for r in rows:
        if any(not r.get(field) for field in FIELDS):
            raise ValueError("Missing provenance or nonpromotion boundary: " + r["record_id"])
        if not r["source_locator"].startswith("https://"):
            raise ValueError("Unqualified source URL: " + r["record_id"])
    return rows

def audit(rows: list[dict[str, str]]) -> dict:
    byid = {row["record_id"]: row for row in rows}
    counts = Counter(r["claim_family"] for r in rows)
    if not set(counts) <= CLAIM_FAMILIES:
        raise ValueError("A non-global or untyped claim family was inserted")
    for a, b, relation, strength in EDGES:
        if a not in byid or b not in byid:
            raise ValueError("Missing original source for positive edge")
        if a == b or byid[a]["source_object_id"] == byid[b]["source_object_id"]:
            raise ValueError("Independent source objects collapsed into one")
        if a == "GP01" and not byid[b]["relation_to_previous"].startswith("named_sequel"):
            raise ValueError("WFA sequel citation lost")
        if a == "GC01" and "direct_named_self_reference" not in byid[b]["relation_to_previous"]:
            raise ValueError("Original author retrospective self-reference unverified")
        if a == "GP03" and "institution" not in byid[b]["source_role"]:
            raise ValueError("Academy disavowal not attributed to original NAS")
    for a, b, _ in UNPAID_TRANSMISSIONS:
        if a not in byid or b not in byid:
            raise ValueError("Missing source for unresolved transmission pair")
    # Same-work root does not make the author list/document version identical.
    if byid["GP04"]["argument_root_family"] != byid["GP06"]["argument_root_family"]:
        raise ValueError("OISM original manuscript and later journal work lineage lost")
    if byid["GP04"]["source_object_id"] == byid["GP06"]["source_object_id"]:
        raise ValueError("Unverified 1998/1999 edition identity promoted")
    if byid["GP03"]["argument_root_family"] == byid["GP01"]["argument_root_family"]:
        raise ValueError("OISM merged into separately financed WFA film campaign")
    if byid["GC01"]["argument_root_family"] == byid["GC04"]["argument_root_family"]:
        raise ValueError("1975 cooling media and 1998-window climate claim conflated")
    if "undated" not in byid["GP07"]["source_date"]:
        raise ValueError("Undated CO2 Coalition webpage assigned false publication year")
    if byid["GP01"]["source_date"] >= byid["GP02"]["source_date"]:
        raise ValueError("Sequel source chronology inverted")
    if "31,000" not in byid["GP03"]["attribution_and_nonpromotion_boundary"] and "31000" not in byid["GP03"]["attribution_and_nonpromotion_boundary"]:
        raise ValueError("Current signatures incorrectly promoted to 1998 count")
    for k in ("GP09", "GP10", "GP11"):
        if not byid[k]["independent_empirical_origin"].startswith("yes"):
            raise ValueError("Original limited empirical plant science missing: " + k)
    if byid["GP07"]["independent_empirical_origin"].startswith("yes"):
        raise ValueError("Advocacy fact sheet promoted to independent plant experiment")
    if byid["GC01"]["independent_empirical_origin"].startswith("yes"):
        raise ValueError("Magazine article promoted to global scientific consensus")
    if "not a global net-welfare" not in byid["GP09"]["attribution_and_nonpromotion_boundary"]:
        raise ValueError("CO2 greening mistaken for total Earth-system benefit")
    root_groups: dict[str, list[str]] = defaultdict(list)
    for r in rows:
        root_groups[r["argument_root_family"]].append(r["record_id"])
    return {
        "status": "global-claims-selected-source-case-study-only",
        "selected_appearances": len(rows),
        "selected_claim_families": dict(sorted(counts.items())),
        "source_objects": len({r["source_object_id"] for r in rows}),
        "argument_family_inventory_not_independent_sources": {
            k: sorted(v) for k, v in sorted(root_groups.items())
        },
        "documented_scoped_relations": [
            {"from": a, "to": b, "type": rel, "basis": strength}
            for a, b, rel, strength in EDGES
        ],
        "unproved_relevant_transmissions": [
            {"from": a, "to": b, "boundary": why}
            for a, b, why in UNPAID_TRANSMISSIONS
        ],
        "global_population_estimate": None,
        "warning": (
            "Deliberately selected world-spanning originals, not a global "
            "representative sample or a count of independently validated "
            "climate denial research. True plant fertilization is not proof "
            "that emissions' net Earth-system impacts are beneficial."
        ),
    }

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER)
    p.add_argument("--json", action="store_true")
    args = p.parse_args()
    report = audit(read_ledger(args.ledger))
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print("Selected worldwide claim appearances:", report["selected_appearances"])
        print("Claim families:", len(report["selected_claim_families"]))
        print("Distinct source-document objects:", report["source_objects"])
        print("Verified scope-bound joins:", len(report["documented_scoped_relations"]))
        print(report["warning"])

if __name__ == "__main__":
    main()
