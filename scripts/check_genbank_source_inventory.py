#!/usr/bin/env python3
"""Read-only independent source-inventory parity for the GenBank parser.

The reference inventory was inspected from Justin Atkin / The Thought
Emporium's GitHub file and preserves creator attribution and exact blob SHA.
This is not a genetic sequence design or an experiment.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from scripts.genbank_readonly_ingest import SCHEMA, parse_genbank_bytes

SCHEMA_VERSION = "dashi.genbank.source-inventory-parity.v1"


def source_location_spelling(ast: dict) -> str:
    """Canonical exact GenBank location view from normalized coordinates."""
    if ast["kind"] == "span":
        location = f"{ast['start1']}..{ast['end1']}"
        return f"complement({location})" if ast["strand"] == -1 else location
    if ast["kind"] != "compound" or ast["operator"] not in ("join", "order"):
        raise ValueError("unsupported source location")
    return (f"{ast['operator']}("
            + ",".join(source_location_spelling(p) for p in ast["parts"])
            + ")")


def git_blob_sha(raw: bytes) -> str:
    return hashlib.sha1(
        b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
    ).hexdigest()


def verify_inspected_source(report: dict, inventory: dict, raw: bytes) -> dict:
    if (report.get("schema") != SCHEMA or
            inventory.get("schema") != "dashi.genbank.creator-source-observation.v1"):
        raise ValueError("unrecognized parser/inventory schema")
    source, obs = inventory["source"], inventory["observed"]
    failures = []

    def check(ok: bool, reason: str):
        if not ok:
            failures.append(reason)

    check(git_blob_sha(raw) == source["git_blob_sha"],
          "original Git blob mismatch")
    check(len(raw) == report["source"]["raw_byte_count"],
          "raw byte count mismatch")
    check(report["molecule"]["sequence_length"] == obs["length_declared"],
          "declared length mismatch")
    check(report["molecule"]["sequence_length"] == obs["length_sequence_letters"],
          "sequence-letter count mismatch")
    check(report["molecule"]["topology"] == obs["topology"],
          "molecule topology mismatch")
    check(report["feature_count"] == obs["feature_count"],
          "feature count mismatch")
    check(report["feature_types"] == obs["feature_types"],
          "feature categories mismatch")
    check(len(report["features"]) == len(inventory["features"]),
          "source-feature inventory length mismatch")

    for found, expected in zip(report["features"], inventory["features"]):
        idx = found["index"]
        check(idx == expected["index"], f"feature {idx}: index mismatch")
        check(found["type"] == expected["type"],
              f"feature {idx}: type mismatch")
        check(source_location_spelling(found["location"]) == expected["raw_location"],
              f"feature {idx}: location, strand or part order mismatch")
        keys = [q["key"] for q in found["qualifiers"]]
        check(keys == expected["qualifier_names"],
              f"feature {idx}: qualifier order mismatch")
        labels = [value for q in found["qualifiers"]
                  if q["key"] == "label" for value in q["values"]]
        source_label = expected["source_label"]
        if source_label is not None:
            check(len(labels) == 1 and labels[0] == source_label.strip('"'),
                  f"feature {idx}: source label mismatch")

    return {
        "schema": SCHEMA_VERSION,
        "original_blob_identity_matches": "original Git blob mismatch" not in failures,
        "all_source_features_match": not failures,
        "problems": failures,
        "parser_receipt_only": True,
        "original_author_attribution_preserved": True,
        "sequence_or_phenotype_authority": False,
        "automatic_ontology_repair": False,
        "source_blob_sha": source["git_blob_sha"],
    }


def main() -> int:
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("input", type=Path)
    cli.add_argument(
        "--inventory", type=Path,
        default=Path(
            "docs/biology/data/"
            "ThoughtEmporiumMagnetoreceptionGenBankSourceInventory.json"
        ),
    )
    args = cli.parse_args()
    raw = args.input.read_bytes()
    inventory = json.loads(args.inventory.read_text(encoding="utf-8"))
    report = parse_genbank_bytes(
        raw,
        source_ref=inventory["source"]["source_uri"],
        creator=inventory["source"]["creator"],
        source_revision=inventory["source"]["source_commit"],
    )
    receipt = verify_inspected_source(report, inventory, raw)
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if receipt["all_source_features_match"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
